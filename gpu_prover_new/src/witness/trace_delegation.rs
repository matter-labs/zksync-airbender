use crate::prover::context::DeviceAllocation;
use crate::witness::trace::ChunkedTraceHolder;

pub struct DelegationTraceDevice<T> {
    pub tracing_data: DeviceAllocation<T>,
}

#[repr(C)]
pub(crate) struct DelegationTraceRaw<T> {
    pub cycles_count: u32,
    pub tracing_data: *const T,
}

impl<T> From<&DelegationTraceDevice<T>> for DelegationTraceRaw<T> {
    fn from(value: &DelegationTraceDevice<T>) -> Self {
        Self {
            cycles_count: value.tracing_data.len() as u32,
            tracing_data: value.tracing_data.as_ptr(),
        }
    }
}

pub(crate) type DelegationTraceHost<T, A> = ChunkedTraceHolder<T, A>;
