#[cfg(not(all(target_endian = "little", target_arch = "riscv32")))]
mod assert {
    compile_error!("unsupported arch - only RV-32 LE is supported");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove(
    dest: *mut core::ffi::c_void,
    src: *const core::ffi::c_void,
    n: usize,
) -> *mut core::ffi::c_void {
    crate::memmove::memmove_impl(dest as *mut u8, src as *const u8, n) as *mut core::ffi::c_void
}
