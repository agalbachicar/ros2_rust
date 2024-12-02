use crate::{Time, Timer};

/// A callback that can be triggered when a timer elapses.
pub enum AnyTimerCallback {
    /// This callback will be triggered repeatedly, each time the period of the
    /// timer elapses.
    Repeating(Box<dyn FnMut(&Timer) + Send>),
    /// This callback will be triggered exactly once, the first time the period
    /// of the timer elapses.
    OneShot(Box<dyn FnOnce(&Timer) + Send>),
    /// Do nothing when the timer elapses. This can be replaced later so that
    /// the timer does something.
    None,
}

/// This trait is used to create timer callbacks for repeating timers. Incoming
/// callbacks can take the current [`Time`] as an argument, or [`Time`], or take
/// no argument at all.
pub trait TimerCallRepeating<Args>: Send + 'static {
    /// Convert a suitable object into a repeating timer callback
    fn into_repeating_timer_callback(self) -> AnyTimerCallback;
}

impl<Func> TimerCallRepeating<()> for Func
where
    Func: FnMut() + Send + 'static,
{
    fn into_repeating_timer_callback(mut self) -> AnyTimerCallback {
        AnyTimerCallback::Repeating(Box::new(move |_| self()))
    }
}

impl<Func> TimerCallRepeating<Timer> for Func
where
    Func: FnMut(&Timer) + Send + 'static,
{
    fn into_repeating_timer_callback(mut self) -> AnyTimerCallback {
        AnyTimerCallback::Repeating(Box::new(move |t| self(t)))
    }
}

/// This trait is used to create timer callbacks for one-shot timers. Incoming
/// callbacks can take the current [`Time`] as an argument, or [`Time`], or take
/// no argument at all.
pub trait TimerCallOnce<Args>: Send + 'static {
    /// Convert a suitable object into a one-shot timer callback
    fn into_oneshot_timer_callback(self) -> AnyTimerCallback;
}

impl<Func> TimerCallOnce<()> for Func
where
    Func: FnOnce() + Send + 'static,
{
    fn into_oneshot_timer_callback(self) -> AnyTimerCallback {
        AnyTimerCallback::OneShot(Box::new(move |_| self()))
    }
}

impl<Func> TimerCallOnce<Timer> for Func
where
    Func: FnOnce(&Timer) + Send + 'static,
{
    fn into_oneshot_timer_callback(self) -> AnyTimerCallback {
        AnyTimerCallback::OneShot(Box::new(move |t| self(t)))
    }
}

impl<Func> TimerCallOnce<Time> for Func
where
    Func: FnOnce(Time) + Send + 'static,
{
    fn into_oneshot_timer_callback(self) -> AnyTimerCallback {
        AnyTimerCallback::OneShot(Box::new(move |t| self(t.handle.clock.now())))
    }
}
