use std::ffi::{c_char, CString};
use std::ptr;
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

#[link(name = "gpu_core_nvtx")]
unsafe extern "C" {
    fn gpu_core_nvtx_domain_create(name: *const c_char) -> NvtxDomainHandle;
    fn gpu_core_nvtx_register_string(
        domain: NvtxDomainHandle,
        string: *const c_char,
    ) -> NvtxStringHandle;
    fn gpu_core_nvtx_domain_ascii_range_start(
        domain: NvtxDomainHandle,
        message: *const c_char,
    ) -> u64;
    fn gpu_core_nvtx_registered_range_start(
        domain: NvtxDomainHandle,
        string: NvtxStringHandle,
    ) -> u64;
    fn gpu_core_nvtx_ascii_range_start(message: *const c_char) -> u64;
    fn gpu_core_nvtx_range_end(id: u64);
}

#[derive(Clone, Copy)]
pub struct RangeId(u64);

struct Registration {
    domain_name: Option<String>,
    message: CString,
    domain: NvtxDomainHandle,
    registered: NvtxStringHandle,
}

// SAFETY: NVTX domain and registered string handles are immutable process-global
// handles after creation. The inner CString is never mutated after registration.
unsafe impl Send for Registration {}
// SAFETY: Handles are treated as immutable opaque pointers after init.
unsafe impl Sync for Registration {}

struct DomainEntry {
    name: String,
    handle: NvtxDomainHandle,
}

// SAFETY: Same justification as `Registration`.
unsafe impl Send for DomainEntry {}
unsafe impl Sync for DomainEntry {}

fn domain_registry() -> &'static Mutex<Vec<DomainEntry>> {
    static DOMAINS: OnceLock<Mutex<Vec<DomainEntry>>> = OnceLock::new();
    DOMAINS.get_or_init(|| Mutex::new(Vec::new()))
}

fn get_or_create_domain(name: &str) -> NvtxDomainHandle {
    let mut domains = domain_registry()
        .lock()
        .expect("NVTX domain registry mutex poisoned");
    if let Some(entry) = domains.iter().find(|entry| entry.name == name) {
        return entry.handle;
    }
    let cstring = CString::new(name).expect("NVTX domain name must not contain NUL");
    // SAFETY: `cstring` is a valid NUL-terminated C string for the call duration.
    let handle = unsafe { gpu_core_nvtx_domain_create(cstring.as_ptr()) };
    domains.push(DomainEntry {
        name: name.to_owned(),
        handle,
    });
    handle
}

fn range_registry() -> &'static Mutex<Vec<Box<Registration>>> {
    static REGISTRY: OnceLock<Mutex<Vec<Box<Registration>>>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(Vec::new()))
}

fn get_or_create_registration(domain: Option<&str>, message: &str) -> *const Registration {
    let mut registry = range_registry()
        .lock()
        .expect("NVTX range registry mutex poisoned");
    if let Some(entry) = registry.iter().find(|entry| {
        entry.domain_name.as_deref() == domain && entry.message.to_bytes() == message.as_bytes()
    }) {
        return &**entry as *const Registration;
    }
    let domain_handle = match domain {
        Some(name) => get_or_create_domain(name),
        None => ptr::null_mut(),
    };
    let message_cstring = CString::new(message).expect("NVTX range message must not contain NUL");
    let registered = if domain_handle.is_null() {
        ptr::null_mut()
    } else {
        // SAFETY: `domain_handle` was produced by NVTX and `message_cstring` is NUL-terminated.
        unsafe { gpu_core_nvtx_register_string(domain_handle, message_cstring.as_ptr()) }
    };
    let entry = Box::new(Registration {
        domain_name: domain.map(str::to_owned),
        message: message_cstring,
        domain: domain_handle,
        registered,
    });
    let ptr = &*entry as *const Registration;
    registry.push(entry);
    ptr
}

pub fn start_range(domain: Option<&str>, message: &str) -> RangeId {
    let registration = get_or_create_registration(domain, message);
    // SAFETY: `registration` points into a `Box<Registration>` that lives for the
    // remainder of the process (we only ever push onto the registry), so the
    // pointer stays valid after the registry lock is released.
    let reg = unsafe { &*registration };
    let id = if !reg.registered.is_null() {
        // SAFETY: `registered` is a valid NVTX registered-string handle in `domain`.
        unsafe { gpu_core_nvtx_registered_range_start(reg.domain, reg.registered) }
    } else if !reg.domain.is_null() {
        // SAFETY: `domain` is valid; `message` is NUL-terminated and lives for 'static.
        unsafe { gpu_core_nvtx_domain_ascii_range_start(reg.domain, reg.message.as_ptr()) }
    } else {
        // SAFETY: `message` is NUL-terminated and lives for 'static.
        unsafe { gpu_core_nvtx_ascii_range_start(reg.message.as_ptr()) }
    };
    RangeId(id)
}

pub fn end_range(id: RangeId) {
    // SAFETY: `id` was returned by a matching `start_range` call.
    unsafe {
        gpu_core_nvtx_range_end(id.0);
    }
}

pub struct ScopedRange {
    id: RangeId,
}

impl Drop for ScopedRange {
    fn drop(&mut self) {
        end_range(self.id);
    }
}

pub fn scoped_range(domain: Option<&str>, message: &str) -> ScopedRange {
    ScopedRange {
        id: start_range(domain, message),
    }
}
