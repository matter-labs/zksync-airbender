use std::collections::HashMap;
use std::ffi::{c_char, CString};
use std::panic::Location;
use std::ptr;
use std::sync::{Mutex, OnceLock, RwLock};

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

#[cfg(not(no_cuda))]
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
    fn gpu_core_nvtx_mem_schema_register(domain: NvtxDomainHandle) -> u64;
    fn gpu_core_nvtx_mem_mark(
        domain: NvtxDomainHandle,
        schema_id: u64,
        site: NvtxStringHandle,
        category: u32,
        id: u64,
        address: u64,
        bytes: u64,
        pool_used_after: u64,
        placement: u32,
    );
    fn gpu_core_nvtx_mem_heap_register(
        domain: NvtxDomainHandle,
        ptr: *const core::ffi::c_void,
        size: usize,
        name: *const c_char,
    ) -> *mut core::ffi::c_void;
    fn gpu_core_nvtx_mem_region_register(
        domain: NvtxDomainHandle,
        heap: *mut core::ffi::c_void,
        ptr: *const core::ffi::c_void,
        size: usize,
    );
    fn gpu_core_nvtx_mem_region_unregister(domain: NvtxDomainHandle, ptr: *const core::ffi::c_void);
    fn gpu_core_nvtx_mem_heap_unregister(domain: NvtxDomainHandle, heap: *mut core::ffi::c_void);
}

// Without the CUDA Toolkit there is no `nvtx3/nvToolsExt.h`, so `build.rs` skips
// `native/nvtx.c` and there is no `gpu_core_nvtx` to link. No-ops rather than
// era_cudart_sys's `unimplemented!()`: NVTX only annotates, and real NVTX is
// inert with no profiler attached. Null handles and a zero id flow correctly
// through the callers below.
#[cfg(no_cuda)]
mod stubs {
    use super::{c_char, NvtxDomainHandle, NvtxStringHandle};
    use std::ptr;

    pub(super) unsafe extern "C" fn gpu_core_nvtx_domain_create(
        _name: *const c_char,
    ) -> NvtxDomainHandle {
        ptr::null_mut()
    }

    #[allow(unused)]
    pub(super) unsafe extern "C" fn gpu_core_nvtx_register_string(
        _domain: NvtxDomainHandle,
        _string: *const c_char,
    ) -> NvtxStringHandle {
        ptr::null_mut()
    }

    #[allow(unused)]
    pub(super) unsafe extern "C" fn gpu_core_nvtx_domain_ascii_range_start(
        _domain: NvtxDomainHandle,
        _message: *const c_char,
    ) -> u64 {
        0
    }

    #[allow(unused)]
    pub(super) unsafe extern "C" fn gpu_core_nvtx_registered_range_start(
        _domain: NvtxDomainHandle,
        _string: NvtxStringHandle,
    ) -> u64 {
        0
    }

    pub(super) unsafe extern "C" fn gpu_core_nvtx_ascii_range_start(
        _message: *const c_char,
    ) -> u64 {
        0
    }

    pub(super) unsafe extern "C" fn gpu_core_nvtx_range_end(_id: u64) {}

    pub(super) unsafe extern "C" fn gpu_core_nvtx_mem_schema_register(
        _domain: NvtxDomainHandle,
    ) -> u64 {
        0
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) unsafe extern "C" fn gpu_core_nvtx_mem_mark(
        _domain: NvtxDomainHandle,
        _schema_id: u64,
        _site: NvtxStringHandle,
        _category: u32,
        _id: u64,
        _address: u64,
        _bytes: u64,
        _pool_used_after: u64,
        _placement: u32,
    ) {
    }

    pub(super) unsafe extern "C" fn gpu_core_nvtx_mem_heap_register(
        _domain: NvtxDomainHandle,
        _ptr: *const core::ffi::c_void,
        _size: usize,
        _name: *const c_char,
    ) -> *mut core::ffi::c_void {
        core::ptr::null_mut()
    }

    pub(super) unsafe extern "C" fn gpu_core_nvtx_mem_region_register(
        _domain: NvtxDomainHandle,
        _heap: *mut core::ffi::c_void,
        _ptr: *const core::ffi::c_void,
        _size: usize,
    ) {
    }

    pub(super) unsafe extern "C" fn gpu_core_nvtx_mem_region_unregister(
        _domain: NvtxDomainHandle,
        _ptr: *const core::ffi::c_void,
    ) {
    }

    pub(super) unsafe extern "C" fn gpu_core_nvtx_mem_heap_unregister(
        _domain: NvtxDomainHandle,
        _heap: *mut core::ffi::c_void,
    ) {
    }
}

#[cfg(no_cuda)]
use stubs::{
    gpu_core_nvtx_ascii_range_start, gpu_core_nvtx_domain_ascii_range_start,
    gpu_core_nvtx_domain_create, gpu_core_nvtx_mem_heap_register,
    gpu_core_nvtx_mem_heap_unregister, gpu_core_nvtx_mem_mark, gpu_core_nvtx_mem_region_register,
    gpu_core_nvtx_mem_region_unregister, gpu_core_nvtx_mem_schema_register,
    gpu_core_nvtx_range_end, gpu_core_nvtx_register_string, gpu_core_nvtx_registered_range_start,
};

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

// `Box<Registration>` is deliberate, not redundant: `get_or_create_registration`
// hands out `*const Registration` pointers into these entries that must stay valid
// for the remainder of the process (see the SAFETY note in `start_range`). Boxing
// gives each entry a stable heap address, so pushing new entries never reallocates
// and invalidates outstanding pointers — a plain `Vec<Registration>` would dangle
// them on growth.
#[allow(clippy::vec_box)]
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

// ---------------------------------------------------------------------------
// Pool-allocation instrumentation (`ab.mem` domain), always on.
//
// Two independent consumers share the domain:
// - `nvtxMemHeapRegister`/regions describe the pool to memory tools — under
//   `compute-sanitizer` (whose `--nvtx` defaults to yes) this enables
//   per-allocation bounds checking inside the pool's single backing
//   allocation.
// - One payload-carrying mark per alloc and per free records the allocation
//   data (correlation id, address, bytes, pool-used-after, placement;
//   category 1 = alloc, 2 = free; message = the `#[track_caller]` alloc site)
//   for nsys — instant events, no timeline bars.
//
// With no tool attached every NVTX call early-outs; the per-event cost on top
// is one read-locked hash lookup for the cached site string — no string
// formatting, no heap allocation.
// ---------------------------------------------------------------------------

pub const MEM_MARK_CATEGORY_ALLOC: u32 = 1;
pub const MEM_MARK_CATEGORY_FREE: u32 = 2;

/// Opaque tool-side heap handle from [`mem_heap_register`] (null without an
/// attached tool; the region calls below accept that).
#[derive(Clone, Copy)]
pub struct MemHeapHandle(*mut core::ffi::c_void);

// SAFETY: the handle is an opaque tool-issued token, only ever passed back to
// NVTX, which supports cross-thread use.
unsafe impl Send for MemHeapHandle {}

impl MemHeapHandle {
    /// NVTX's process-wide pseudo-heap (a null handle) — the fallback when an
    /// address cannot be matched to a registered backing range.
    pub fn process_wide() -> Self {
        Self(ptr::null_mut())
    }
}

fn mem_domain() -> NvtxDomainHandle {
    static DOMAIN: OnceLock<usize> = OnceLock::new();
    *DOMAIN.get_or_init(|| get_or_create_domain("ab.mem") as usize) as NvtxDomainHandle
}

fn mem_schema_id() -> u64 {
    static SCHEMA: OnceLock<u64> = OnceLock::new();
    // SAFETY: valid process-global domain handle.
    *SCHEMA.get_or_init(|| unsafe { gpu_core_nvtx_mem_schema_register(mem_domain()) })
}

fn mem_site_registry() -> &'static RwLock<HashMap<usize, usize>> {
    static SITES: OnceLock<RwLock<HashMap<usize, usize>>> = OnceLock::new();
    SITES.get_or_init(|| RwLock::new(HashMap::new()))
}

fn get_or_register_mem_site(site: &'static Location<'static>) -> NvtxStringHandle {
    let key = site as *const Location as usize;
    if let Some(&handle) = mem_site_registry()
        .read()
        .expect("NVTX mem site registry poisoned")
        .get(&key)
    {
        return handle as NvtxStringHandle;
    }
    let message = format!("{}:{}", site.file(), site.line());
    let cstring = CString::new(message).expect("NVTX mem site message must not contain NUL");
    // SAFETY: domain handle from NVTX; `cstring` is NUL-terminated for the call.
    let handle = unsafe { gpu_core_nvtx_register_string(mem_domain(), cstring.as_ptr()) };
    mem_site_registry()
        .write()
        .expect("NVTX mem site registry poisoned")
        .entry(key)
        .or_insert(handle as usize);
    handle
}

/// Describes one pool backing range to memory tools as a sub-allocator heap.
pub fn mem_heap_register(ptr: *const u8, size: usize, name: &str) -> MemHeapHandle {
    let cstring = CString::new(name).expect("NVTX mem heap name must not contain NUL");
    // SAFETY: `ptr`/`size` describe a live backing allocation; `cstring` is
    // NUL-terminated for the call duration (NVTX copies ascii messages).
    let handle = unsafe {
        gpu_core_nvtx_mem_heap_register(mem_domain(), ptr.cast(), size, cstring.as_ptr())
    };
    MemHeapHandle(handle)
}

/// Registers one pool allocation as a region of its heap.
pub fn mem_region_register(heap: MemHeapHandle, ptr: *const u8, size: usize) {
    // SAFETY: `heap` came from `mem_heap_register`; `ptr`/`size` describe the
    // suballocation just handed out.
    unsafe { gpu_core_nvtx_mem_region_register(mem_domain(), heap.0, ptr.cast(), size) }
}

/// Unregisters a heap registered via [`mem_heap_register`].
pub fn mem_heap_unregister(heap: MemHeapHandle) {
    if heap.0.is_null() {
        return;
    }
    // SAFETY: `heap` came from `mem_heap_register`.
    unsafe { gpu_core_nvtx_mem_heap_unregister(mem_domain(), heap.0) }
}

/// Unregisters the region at `ptr` (referenced by address, per the NVTX
/// virtual-address region contract).
pub fn mem_region_unregister(ptr: *const u8) {
    // SAFETY: `ptr` was registered via `mem_region_register` and not yet freed.
    unsafe { gpu_core_nvtx_mem_region_unregister(mem_domain(), ptr.cast()) }
}

/// Emits one alloc/free mark carrying the allocation record.
pub fn mem_mark(
    category: u32,
    site: &'static Location<'static>,
    id: u64,
    address: u64,
    bytes: usize,
    pool_used_after: usize,
    placement_tag: u8,
) {
    let string = get_or_register_mem_site(site);
    // SAFETY: domain, schema and registered-string handles are valid
    // process-global NVTX handles created above.
    unsafe {
        gpu_core_nvtx_mem_mark(
            mem_domain(),
            mem_schema_id(),
            string,
            category,
            id,
            address,
            bytes as u64,
            pool_used_after as u64,
            placement_tag as u32,
        )
    }
}
