use crate::{
    clock::Clock, context::ContextHandle, error::RclrsError, log_error, rcl_bindings::*,
    ToLogParams, ToResult, ENTITY_LIFECYCLE_MUTEX,
};
// TODO: fix me when the callback type is properly defined.
// use std::fmt::Debug;
use std::{
    sync::{atomic::AtomicBool, Arc, Mutex},
    time::Duration,
};

mod timer_callback;
pub use timer_callback::*;

mod timer_options;
pub use timer_options::*;

/// Struct for executing periodic events.
///
/// The execution of the callbacks is tied to [`spin_once`][1] or [`spin`][2] on the timers's node.
///
/// Timer can be created via [`Node::create_timer()`][3], this is to ensure that [`Node`][4]s can
/// track all the timers that have been created. However, a user of a `Timer` can also
/// use it standalone.
///
/// [1]: crate::spin_once
/// [2]: crate::spin
/// [3]: crate::Node::create_timer
/// [4]: crate::Node
// TODO: callback type prevents us from making the Timer implement the Debug trait.
// #[derive(Debug)]
pub struct Timer {
    pub(crate) handle: TimerHandle,
    /// The callback function that runs when the timer is due.
    callback: Arc<Mutex<Option<AnyTimerCallback>>>,
    /// What was the last time lapse between calls to this timer
    last_elapse: Mutex<Duration>,
    /// We hold onto the Timer's clock for the whole lifespan of the Timer to
    /// make sure the underlying `rcl_clock_t` remains valid.
    pub(crate) in_use_by_wait_set: Arc<AtomicBool>,
}

/// Manage the lifecycle of an `rcl_timer_t`, including managing its dependency
/// on `rcl_clock_t` by ensuring that this dependency are [dropped after][1]
/// the `rcl_timer_t`.
///
/// [1]: <https://doc.rust-lang.org/reference/destructors.html>
pub(crate) struct TimerHandle {
    pub(crate) rcl_timer: Arc<Mutex<rcl_timer_t>>,
    clock: Clock,
}

impl Timer {
    /// Gets the period of the timer
    pub fn get_timer_period(&self) -> Result<Duration, RclrsError> {
        let mut timer_period_ns = 0;
        unsafe {
            let rcl_timer = self.handle.rcl_timer.lock().unwrap();
            rcl_timer_get_period(&*rcl_timer, &mut timer_period_ns)
        }
        .ok()?;

        rcl_duration(timer_period_ns)
    }

    /// Cancels the timer, stopping the execution of the callback
    pub fn cancel(&self) -> Result<(), RclrsError> {
        let mut rcl_timer = self.handle.rcl_timer.lock().unwrap();
        let cancel_result = unsafe { rcl_timer_cancel(&mut *rcl_timer) }.ok()?;
        Ok(cancel_result)
    }

    /// Checks whether the timer is canceled or not
    pub fn is_canceled(&self) -> Result<bool, RclrsError> {
        let mut is_canceled = false;
        unsafe {
            let rcl_timer = self.handle.rcl_timer.lock().unwrap();
            rcl_timer_is_canceled(&*rcl_timer, &mut is_canceled)
        }
        .ok()?;
        Ok(is_canceled)
    }

    /// Get the last time lapse between calls to the timer.
    ///
    /// This is different from [`Self::time_since_last_call`] because it remains
    /// constant between calls to the Timer.
    ///
    /// It keeps track of the what the value of [`Self::time_since_last_call`]
    /// was immediately before the most recent call to the callback. This will
    /// be [`Duration::ZERO`] if the `Timer` has never been triggered.
    pub fn last_elapse(&self) -> Duration {
        *self.last_elapse.lock().unwrap()
    }

    /// Retrieves the time since the last call to the callback
    pub fn time_since_last_call(&self) -> Result<Duration, RclrsError> {
        let mut time_value_ns: i64 = 0;
        unsafe {
            let rcl_timer = self.handle.rcl_timer.lock().unwrap();
            rcl_timer_get_time_since_last_call(&*rcl_timer, &mut time_value_ns)
        }
        .ok()?;

        rcl_duration(time_value_ns)
    }

    /// Retrieves the time until the next call of the callback
    pub fn time_until_next_call(&self) -> Result<Duration, RclrsError> {
        let mut time_value_ns: i64 = 0;
        unsafe {
            let rcl_timer = self.handle.rcl_timer.lock().unwrap();
            rcl_timer_get_time_until_next_call(&*rcl_timer, &mut time_value_ns)
        }
        .ok()?;

        rcl_duration(time_value_ns)
    }

    /// Resets the timer.
    pub fn reset(&self) -> Result<(), RclrsError> {
        let mut rcl_timer = self.handle.rcl_timer.lock().unwrap();
        unsafe { rcl_timer_reset(&mut *rcl_timer) }.ok()
    }

    /// Checks if the timer is ready (not canceled)
    pub fn is_ready(&self) -> Result<bool, RclrsError> {
        let is_ready = unsafe {
            let mut is_ready: bool = false;
            let rcl_timer = self.handle.rcl_timer.lock().unwrap();
            rcl_timer_is_ready(&*rcl_timer, &mut is_ready).ok()?;
            is_ready
        };

        Ok(is_ready)
    }

    /// Get the clock that this timer runs on.
    pub fn clock(&self) -> &Clock {
        &self.handle.clock
    }

    /// Set a new callback for the timer. This will return whatever callback
    /// was already present unless you are calling the function from inside of
    /// the timer's callback, in which case you will receive [`None`].
    ///
    /// See also:
    /// * [`Self::set_repeating`]
    /// * [`Self::set_oneshot`]
    /// * [`Self::set_inert`].
    pub fn set_callback(&self, callback: AnyTimerCallback) -> Option<AnyTimerCallback> {
        self.callback.lock().unwrap().replace(callback)
    }

    /// Set a repeating callback for this timer.
    ///
    /// See also:
    /// * [`Self::set_oneshot`]
    /// * [`Self::set_inert`]
    pub fn set_repeating<Args>(
        &self,
        f: impl TimerCallRepeating<Args>,
    ) -> Option<AnyTimerCallback> {
        self.set_callback(f.into_repeating_timer_callback())
    }

    /// Set a one-shot callback for the timer.
    ///
    /// The next time the timer is triggered, the callback will be set to
    /// [`AnyTimerCallback::None`] after this callback is triggered. To keep the
    /// timer useful, you can reset the Timer callback at any time, including
    /// inside the one-shot callback itself.
    ///
    /// See also:
    /// * [`Self::set_repeating`]
    /// * [`Self::set_inert`]
    pub fn set_oneshot<Args>(&self, f: impl TimerCallOnce<Args>) -> Option<AnyTimerCallback> {
        self.set_callback(f.into_oneshot_timer_callback())
    }

    /// Remove the callback from the timer.
    ///
    /// This does not cancel the timer; it will continue to wake up and be
    /// triggered at its regular period. However, nothing will happen when the
    /// timer is triggered until you give a new callback to the timer.
    ///
    /// You can give the timer a new callback at any time by calling:
    /// * [`Self::set_repeating`]
    /// * [`Self::set_oneshot`]
    pub fn set_inert(&self) -> Option<AnyTimerCallback> {
        self.set_callback(AnyTimerCallback::None)
    }

    /// This is triggerd when the Timer wakes up its wait set.
    pub(crate) fn execute(&self) -> Result<(), RclrsError> {
        if self.is_ready()? {
            self.call()?;
        }

        Ok(())
    }

    /// Creates a new timer. Users should call one of [`Node::create_timer`],
    /// [`Node::create_timer_repeating`], [`Node::create_timer_oneshot`], or
    /// [`Node::create_timer_inert`].
    pub(crate) fn new(
        context: &ContextHandle,
        period: Duration,
        clock: Clock,
        callback: AnyTimerCallback,
    ) -> Result<Timer, RclrsError> {
        let period = period.as_nanos() as i64;

        // Callbacks will be handled at the rclrs layer.
        let rcl_timer_callback: rcl_timer_callback_t = None;

        let rcl_timer = Arc::new(Mutex::new(
            // SAFETY: Zero-initializing a timer is always safe
            unsafe { rcl_get_zero_initialized_timer() },
        ));

        unsafe {
            let mut rcl_clock = clock.get_rcl_clock().lock().unwrap();
            let mut rcl_context = context.rcl_context.lock().unwrap();

            // SAFETY: Getting a default value is always safe.
            let allocator = rcutils_get_default_allocator();

            let _lifecycle = ENTITY_LIFECYCLE_MUTEX.lock().unwrap();
            // SAFETY: We lock the lifecycle mutex since rcl_timer_init is not
            // thread-safe.
            rcl_timer_init(
                &mut *rcl_timer.lock().unwrap(),
                &mut *rcl_clock,
                &mut *rcl_context,
                period,
                rcl_timer_callback,
                allocator,
            )
        }
        .ok()?;

        let timer = Timer {
            handle: TimerHandle { rcl_timer, clock },
            callback: Arc::new(Mutex::new(Some(callback))),
            last_elapse: Mutex::new(Duration::ZERO),
            in_use_by_wait_set: Arc::new(AtomicBool::new(false)),
        };
        Ok(timer)
    }

    /// Force the timer to be called, even if it is not ready to be triggered yet.
    /// We could consider making this public, but the behavior may confuse users.
    fn call(&self) -> Result<(), RclrsError> {
        // Keep track of the time elapsed since the last call. We need to run
        // this before we trigger rcl_call.
        let last_elapse = self.time_since_last_call().unwrap_or(Duration::ZERO);
        *self.last_elapse.lock().unwrap() = last_elapse;

        if let Err(err) = self.rcl_call() {
            log_error!("timer", "Unable to call timer: {err:?}",);
        }

        let Some(callback) = self.callback.lock().unwrap().take() else {
            log_error!(
                "timer".once(),
                "Timer is missing its callback information. This should not \
                be possible, please report it to the maintainers of rclrs.",
            );
            return Ok(());
        };

        match callback {
            AnyTimerCallback::Repeating(mut callback) => {
                callback(self);
                self.restore_callback(AnyTimerCallback::Repeating(callback));
            }
            AnyTimerCallback::OneShot(callback) => {
                callback(self);
                // We restore the callback as None because this was a
                // one-shot which has been consumed.
                self.restore_callback(AnyTimerCallback::None);
            }
            AnyTimerCallback::None => {
                // Nothing to do here, just restore the callback.
                self.restore_callback(AnyTimerCallback::None);
            }
        }

        Ok(())
    }

    /// Updates the state of the rcl_timer to know that it has been called. This
    /// should only be called by [`Self::call`].
    ///
    /// The callback held by the rcl_timer is null because we store the callback
    /// in the [`Timer`] struct. This means there are no side-effects to this
    /// except to keep track of when the timer has been called.
    fn rcl_call(&self) -> Result<(), RclrsError> {
        let mut rcl_timer = self.handle.rcl_timer.lock().unwrap();
        unsafe { rcl_timer_call(&mut *rcl_timer) }.ok()
    }

    /// Used by [`Timer::execute`] to restore the state of the callback if and
    /// only if the user has not already set a new callback.
    fn restore_callback(&self, callback: AnyTimerCallback) {
        let mut self_callback = self.callback.lock().unwrap();
        if self_callback.is_none() {
            *self_callback = Some(callback);
        }
    }
}

/// 'Drop' trait implementation to be able to release the resources
impl Drop for TimerHandle {
    fn drop(&mut self) {
        let _lifecycle = ENTITY_LIFECYCLE_MUTEX.lock().unwrap();
        // SAFETY: The lifecycle mutex is locked and the clock for the timer
        // must still be valid because TimerHandle keeps it alive.
        unsafe { rcl_timer_fini(&mut *self.rcl_timer.lock().unwrap()) };
    }
}

impl PartialEq for Timer {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.handle.rcl_timer, &other.handle.rcl_timer)
    }
}

fn rcl_duration(duration_value_ns: i64) -> Result<Duration, RclrsError> {
    if duration_value_ns < 0 {
        Err(RclrsError::NegativeDuration(duration_value_ns))
    } else {
        Ok(Duration::from_nanos(duration_value_ns as u64))
    }
}

// SAFETY: The functions accessing this type, including drop(), shouldn't care about the thread
// they are running in. Therefore, this type can be safely sent to another thread.
unsafe impl Send for rcl_timer_t {}

#[cfg(test)]
mod tests {
    use crate::*;
    use std::{
        sync::atomic::{AtomicBool, Ordering},
        thread, time,
    };

    #[test]
    fn traits() {
        use crate::test_helpers::*;

        assert_send::<Timer>();
        assert_sync::<Timer>();
    }

    #[test]
    fn test_new_with_system_clock() {
        let context = Context::new(vec![]).unwrap();
        let result = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            Clock::system(),
            (|| {}).into_repeating_timer_callback(),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_with_steady_clock() {
        let context = Context::new(vec![]).unwrap();
        let result = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_with_source_clock() {
        let (clock, source) = Clock::with_source();
        // No manual time set, it should default to 0
        assert_eq!(clock.now().nsec, 0);
        let set_time = 1234i64;
        source.set_ros_time_override(set_time);

        // ROS time is set, should return the value that was set
        assert_eq!(clock.now().nsec, set_time);

        let context = Context::new(vec![]).unwrap();
        let result = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            clock,
            (|| {}).into_repeating_timer_callback(),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_get_period() {
        let period = Duration::from_millis(1);
        let context = Context::new(vec![]).unwrap();

        let result = Timer::new(
            &context.handle,
            period,
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        );

        let timer = result.unwrap();
        let timer_period = timer.get_timer_period().unwrap();
        assert_eq!(timer_period, period);
    }

    #[test]
    fn test_cancel() {
        let context = Context::new(vec![]).unwrap();

        let result = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        );

        let timer = result.unwrap();
        assert!(!timer.is_canceled().unwrap());
        timer.cancel().unwrap();
        assert!(timer.is_canceled().unwrap());
    }

    #[test]
    fn test_time_since_last_call_before_first_event() {
        let context = Context::new(vec![]).unwrap();

        let result = Timer::new(
            &context.handle,
            Duration::from_millis(2),
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        );
        let timer = result.unwrap();

        let sleep_period = time::Duration::from_millis(1);
        thread::sleep(sleep_period);

        let time_since_last_call = timer.time_since_last_call().unwrap();
        assert!(
            time_since_last_call >= sleep_period,
            "time_since_last_call: {:?} vs sleep period: {:?}",
            time_since_last_call,
            sleep_period,
        );
    }

    #[test]
    fn test_time_until_next_call_before_first_event() {
        let context = Context::new(vec![]).unwrap();
        let period = Duration::from_millis(2);

        let result = Timer::new(
            &context.handle,
            period,
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        );
        let timer = result.unwrap();

        let time_until_next_call = timer.time_until_next_call().unwrap();
        assert!(
            time_until_next_call <= period,
            "time_until_next_call: {:?} vs period: {:?}",
            time_until_next_call,
            period,
        );
    }

    #[test]
    fn test_reset() {
        let context = Context::new(vec![]).unwrap();
        let period = Duration::from_millis(2);
        let timer = Timer::new(
            &context.handle,
            period,
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        )
        .unwrap();

        // The unwrap will panic if the remaining time is negative
        timer.time_until_next_call().unwrap();

        // Sleep until we're past the timer period
        thread::sleep(Duration::from_millis(3));

        // Now the time until next call should give an error
        assert!(matches!(
            timer.time_until_next_call(),
            Err(RclrsError::NegativeDuration(_))
        ));

        // Reset the timer so its interval begins again
        assert!(timer.reset().is_ok());

        // The unwrap will panic if the remaining time is negative
        timer.time_until_next_call().unwrap();
    }

    #[test]
    fn test_call() {
        let context = Context::new(vec![]).unwrap();
        let timer = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        )
        .unwrap();

        // The unwrap will panic if the remaining time is negative
        timer.time_until_next_call().unwrap();

        // Sleep until we're past the timer period
        thread::sleep(time::Duration::from_micros(1500));

        // Now the time until the next call should give an error
        assert!(matches!(
            timer.time_until_next_call(),
            Err(RclrsError::NegativeDuration(_))
        ));

        // The unwrap will panic if anything went wrong with the call
        timer.call().unwrap();

        // The unwrap will panic if the remaining time is negative
        timer.time_until_next_call().unwrap();
    }

    #[test]
    fn test_is_ready() {
        let context = Context::new(vec![]).unwrap();
        let timer = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            Clock::steady(),
            (|| {}).into_repeating_timer_callback(),
        )
        .unwrap();

        assert!(!timer.is_ready().unwrap());

        // Sleep until the period has elapsed
        thread::sleep(Duration::from_micros(1100));

        assert!(timer.is_ready().unwrap());
    }

    #[test]
    fn test_callback() {
        let clock = Clock::steady();
        let initial_time = clock.now();
        let context = Context::new(vec![]).unwrap();
        let executed = Arc::new(AtomicBool::new(false));

        let timer = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            clock,
            create_timer_callback_for_testing(initial_time, Arc::clone(&executed)),
        )
        .unwrap();

        timer.call().unwrap();
        assert!(executed.load(Ordering::Acquire));
    }

    #[test]
    fn test_execute_when_is_not_ready() {
        let clock = Clock::steady();
        let initial_time = clock.now();
        let context = Context::new(vec![]).unwrap();
        let executed = Arc::new(AtomicBool::new(false));

        let timer = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            clock,
            create_timer_callback_for_testing(initial_time, Arc::clone(&executed)),
        )
        .unwrap();

        timer.execute().unwrap();
        assert!(!executed.load(Ordering::Acquire));
    }

    #[test]
    fn test_execute_when_is_ready() {
        let clock = Clock::steady();
        let initial_time = clock.now();
        let context = Context::new(vec![]).unwrap();
        let executed = Arc::new(AtomicBool::new(false));

        let timer = Timer::new(
            &context.handle,
            Duration::from_millis(1),
            clock,
            create_timer_callback_for_testing(initial_time, Arc::clone(&executed)),
        )
        .unwrap();

        thread::sleep(time::Duration::from_millis(2));

        timer.execute().unwrap();
        assert!(executed.load(Ordering::Acquire));
    }

    fn create_timer_callback_for_testing(
        initial_time: Time,
        executed: Arc<AtomicBool>,
    ) -> AnyTimerCallback {
        (move |t: Time| {
            assert!(t
                .compare_with(&initial_time, |t, initial| t >= initial)
                .unwrap());
            executed.store(true, Ordering::Release);
        })
        .into_oneshot_timer_callback()
    }
}
