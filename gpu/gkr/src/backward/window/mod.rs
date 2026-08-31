pub(crate) mod bank;
pub(crate) mod binding;
pub(crate) mod coefficient_bank;
pub(crate) mod common;
pub(crate) mod generated_registry;
pub(crate) mod state;
pub(crate) mod tail;

/// # Safety
///
/// The all-zero bit pattern must be a valid `T`.
pub(crate) unsafe fn zeroed_box<T>() -> Box<T> {
    let layout = std::alloc::Layout::new::<T>();
    let ptr = std::alloc::alloc_zeroed(layout) as *mut T;
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    Box::from_raw(ptr)
}
