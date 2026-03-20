use super::{Counters, State};

/// ExecutionObserver lets a VM publish optional instrumentation without turning
/// it into semantic machine state.
///
/// Methods are receiver-free so the default `()` observer compiles away, while
/// specialized observers can source their storage from a scoped context.
pub trait ExecutionObserver<C: Counters>: 'static {
    #[inline(always)]
    fn on_marker(_state: &State<C>) {}

    #[inline(always)]
    fn on_delegation(_state: &State<C>, _csr: u32, _by: u64) {}
}

impl<C: Counters> ExecutionObserver<C> for () {}
