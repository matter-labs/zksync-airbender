#[cfg(not(all(target_endian = "little", target_arch = "riscv32")))]
mod assert {
    compile_error!("unsupported arch - only RV-32 LE is supported");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset(
    dest: *mut core::ffi::c_void,
    value: core::ffi::c_int,
    n: usize,
) -> *mut core::ffi::c_void {
    crate::memset::memset_impl(dest as *mut u8, value as core::ffi::c_uint as u32, n)
        as *mut core::ffi::c_void
}
