use std::ffi::CString;

#[cfg(not(no_cuda))]
unsafe extern "C" {
    fn ab_gkr_windowed_nvtx_range_start(message: *const std::ffi::c_char) -> u64;
    fn ab_gkr_windowed_nvtx_range_end(id: u64);
}

#[cfg(no_cuda)]
unsafe fn ab_gkr_windowed_nvtx_range_start(_message: *const std::ffi::c_char) -> u64 {
    0
}

#[cfg(no_cuda)]
unsafe fn ab_gkr_windowed_nvtx_range_end(_id: u64) {}

pub struct NvtxRange {
    id: u64,
}

impl NvtxRange {
    pub fn start(name: &str) -> Result<Self, std::ffi::NulError> {
        let name = CString::new(name)?;
        let id = unsafe { ab_gkr_windowed_nvtx_range_start(name.as_ptr()) };
        Ok(Self { id })
    }
}

impl Drop for NvtxRange {
    fn drop(&mut self) {
        unsafe { ab_gkr_windowed_nvtx_range_end(self.id) };
    }
}
