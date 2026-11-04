#[cfg(not(target_endian = "little"))]
mod assert {
    compile_error!("unsupported arch - only LE is supported");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    crate::memcpy::memcpy_impl(dest, src, n)
}
