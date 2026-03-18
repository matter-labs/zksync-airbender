use std::ffi::{c_char, CStr};
use std::ptr::null_mut;
use std::sync::OnceLock;

#[repr(C)]
struct NvtxDomainRegistration {
    _private: [u8; 0],
}

#[repr(C)]
struct NvtxStringRegistration {
    _private: [u8; 0],
}

type NvtxDomainHandle = *mut NvtxDomainRegistration;
type NvtxStringHandle = *mut NvtxStringRegistration;
type NvtxRangeId = u64;

#[link(name = "gpu_prover_nvtx")]
unsafe extern "C" {
    fn gpu_prover_nvtx_register_string(
        domain: NvtxDomainHandle,
        string: *const c_char,
    ) -> NvtxStringHandle;
    fn gpu_prover_nvtx_registered_range_start(
        domain: NvtxDomainHandle,
        string: NvtxStringHandle,
    ) -> NvtxRangeId;
    fn gpu_prover_nvtx_ascii_range_start(message: *const c_char) -> NvtxRangeId;
    fn gpu_prover_nvtx_range_end(id: NvtxRangeId);
}

enum RegisteredRangeMessage {
    Registered(NvtxStringHandle),
    Ascii(&'static CStr),
}

struct RegisteredRangeMetadata {
    domain: NvtxDomainHandle,
    message: RegisteredRangeMessage,
}

// SAFETY: NVTX domain and registered string handles are immutable process-global
// handles after creation, and this helper only reads them after one-time init.
unsafe impl Send for RegisteredRangeMetadata {}
// SAFETY: The handles are treated as immutable opaque pointers after init.
unsafe impl Sync for RegisteredRangeMetadata {}

pub(crate) struct RegisteredRangeGuard {
    id: NvtxRangeId,
}

impl Drop for RegisteredRangeGuard {
    fn drop(&mut self) {
        // SAFETY: `id` is returned by `nvtxDomainRangeStartEx` for this process range.
        unsafe {
            gpu_prover_nvtx_range_end(self.id);
        }
    }
}

pub(crate) fn start_registered_range(
    _domain_name: &'static CStr,
    message_name: &'static CStr,
) -> RegisteredRangeGuard {
    static REGISTRY: OnceLock<RegisteredRangeMetadata> = OnceLock::new();
    let metadata = REGISTRY.get_or_init(|| {
        let domain = null_mut();

        // SAFETY: The global NVTX domain is represented by a null handle, and the message is static.
        let message = unsafe { gpu_prover_nvtx_register_string(domain, message_name.as_ptr()) };
        let message = if message.is_null() {
            RegisteredRangeMessage::Ascii(message_name)
        } else {
            RegisteredRangeMessage::Registered(message)
        };

        RegisteredRangeMetadata { domain, message }
    });

    let id = match metadata.message {
        // SAFETY: `metadata` contains valid process-global handles created during one-time init.
        RegisteredRangeMessage::Registered(message) => unsafe {
            gpu_prover_nvtx_registered_range_start(metadata.domain, message)
        },
        // SAFETY: `message` is a static NUL-terminated C string.
        RegisteredRangeMessage::Ascii(message) => unsafe {
            gpu_prover_nvtx_ascii_range_start(message.as_ptr())
        },
    };
    RegisteredRangeGuard { id }
}
