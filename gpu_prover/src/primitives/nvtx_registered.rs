use std::ffi::{c_char, CStr};
use std::sync::{Mutex, OnceLock};

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
    fn gpu_prover_nvtx_domain_create(name: *const c_char) -> NvtxDomainHandle;
    fn gpu_prover_nvtx_register_string(
        domain: NvtxDomainHandle,
        string: *const c_char,
    ) -> NvtxStringHandle;
    fn gpu_prover_nvtx_domain_ascii_range_start(
        domain: NvtxDomainHandle,
        message: *const c_char,
    ) -> NvtxRangeId;
    fn gpu_prover_nvtx_registered_range_start(
        domain: NvtxDomainHandle,
        string: NvtxStringHandle,
    ) -> NvtxRangeId;
    fn gpu_prover_nvtx_ascii_range_start(message: *const c_char) -> NvtxRangeId;
    fn gpu_prover_nvtx_range_end(id: NvtxRangeId);
}

#[derive(Clone, Copy)]
enum RegisteredRangeMessage {
    Registered(NvtxStringHandle),
    DomainAscii(&'static CStr),
    GlobalAscii(&'static CStr),
}

#[derive(Clone, Copy)]
struct RegisteredRangeMetadata {
    domain_name: &'static CStr,
    message_name: &'static CStr,
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
    domain_name: &'static CStr,
    message_name: &'static CStr,
) -> RegisteredRangeGuard {
    static REGISTRY: OnceLock<Mutex<Vec<RegisteredRangeMetadata>>> = OnceLock::new();
    let registry = REGISTRY.get_or_init(|| Mutex::new(Vec::new()));
    let mut registry = registry.lock().unwrap();

    let metadata = registry
        .iter()
        .find(|metadata| {
            metadata.domain_name.to_bytes() == domain_name.to_bytes()
                && metadata.message_name.to_bytes() == message_name.to_bytes()
        })
        .cloned()
        .unwrap_or_else(|| {
            // SAFETY: The domain name is a static NUL-terminated C string.
            let domain = unsafe { gpu_prover_nvtx_domain_create(domain_name.as_ptr()) };

            // SAFETY: The domain handle comes from NVTX and the message is static.
            let message = unsafe { gpu_prover_nvtx_register_string(domain, message_name.as_ptr()) };
            let message = if !message.is_null() {
                RegisteredRangeMessage::Registered(message)
            } else if !domain.is_null() {
                RegisteredRangeMessage::DomainAscii(message_name)
            } else {
                RegisteredRangeMessage::GlobalAscii(message_name)
            };

            let metadata = RegisteredRangeMetadata {
                domain_name,
                message_name,
                domain,
                message,
            };
            registry.push(metadata.clone());
            metadata
        });

    drop(registry);

    let id = match metadata.message {
        // SAFETY: `metadata` contains valid process-global handles created during one-time init.
        RegisteredRangeMessage::Registered(message) => unsafe {
            gpu_prover_nvtx_registered_range_start(metadata.domain, message)
        },
        // SAFETY: `metadata.domain` is a valid NVTX domain handle and the message is static.
        RegisteredRangeMessage::DomainAscii(message) => unsafe {
            gpu_prover_nvtx_domain_ascii_range_start(metadata.domain, message.as_ptr())
        },
        // SAFETY: `message` is a static NUL-terminated C string.
        RegisteredRangeMessage::GlobalAscii(message) => unsafe {
            gpu_prover_nvtx_ascii_range_start(message.as_ptr())
        },
    };
    RegisteredRangeGuard { id }
}
