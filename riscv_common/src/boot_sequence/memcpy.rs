#[cfg(not(target_endian = "little"))]
mod assert {
    compile_error!("unsupported arch - only LE is supported");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcpy(dest: *mut core::ffi::c_void, src: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void {
    crate::memcpy::memcpy_impl(dest as *mut u8, src as *const u8, n) as *mut core::ffi::c_void
}
