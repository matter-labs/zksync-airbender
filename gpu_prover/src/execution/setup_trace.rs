//! Host storage for a circuit's setup trace.
//!
//! A setup trace is the largest per-circuit host structure the prover keeps: one per
//! (registered binary, circuit type). Retained traces contain only the meaningful
//! columns. The CPU row-major construction buffer may have a larger padded width,
//! but that padding is omitted when transposing into either storage variant.
//!
//! By default a trace lives in page-locked (`cudaHostAlloc`) memory, so the per-proof H2D
//! copy is a real asynchronous DMA. That memory can never be reclaimed. Neither can
//! ordinary anonymous memory on a host with no swap device — evicting an anonymous page
//! requires somewhere to put it — so simply un-pinning these buffers would not give a
//! swap-free host one byte back.
//!
//! Setting `AIRBENDER_SETUP_TRACE_DIR` stores each trace in a mapped file instead. The
//! trace is transposed straight into the mapping, the file is unlinked immediately (the
//! mapping keeps the inode alive, so nothing is left behind if the process dies), and the
//! pages are then ordinary file-backed page cache. Clean file-backed pages *are*
//! reclaimable without swap: under pressure the kernel drops them and faults them back
//! from the file on demand, which is the whole point on a host that has no swap.
//!
//! The cost is that the per-proof copy now reads from pageable memory, which
//! `cudaMemcpyAsync` stages through an internal buffer synchronously instead of DMAing
//! directly, and a fault-back costs a read from the backing file. Whether that tradeoff
//! is worthwhile depends on the host, so this is a runtime switch rather than a build-time one.

use crate::execution::A;
use era_cudart::slice::CudaSlice;
use field::Mersenne31Field;
use std::env;
use std::fs::OpenOptions;
use std::os::fd::AsRawFd;
use std::path::PathBuf;
use std::ptr;
use std::slice;
use std::sync::atomic::{AtomicU64, Ordering};

type BF = Mersenne31Field;

/// Directory for file-backed setup traces, or `None` to keep them page-locked.
pub fn setup_trace_dir() -> Option<PathBuf> {
    match env::var("AIRBENDER_SETUP_TRACE_DIR") {
        Ok(dir) if !dir.is_empty() => Some(PathBuf::from(dir)),
        _ => None,
    }
}

/// A setup trace in an unlinked mapped file.
///
/// The mapping is read-only once built, and is the only thing keeping the backing inode
/// alive; `munmap` on drop releases both.
pub struct MappedSetupTrace {
    ptr: *mut libc::c_void,
    /// Size of the mapping, rounded up to a page. Not the logical length.
    mapped_bytes: usize,
    /// Number of compact `BF` values, excluding any page-alignment tail in the mapping.
    len: usize,
}

// The mapping is read-only for its whole visible lifetime, so handing out `&[BF]` from
// several threads is sound; the raw pointer is what stops the compiler seeing that.
unsafe impl Send for MappedSetupTrace {}
unsafe impl Sync for MappedSetupTrace {}

impl Drop for MappedSetupTrace {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.ptr, self.mapped_bytes);
        }
    }
}

impl MappedSetupTrace {
    fn as_slice(&self) -> &[BF] {
        unsafe { slice::from_raw_parts(self.ptr as *const BF, self.len) }
    }
}

/// Where a circuit's setup trace lives.
pub enum SetupTrace {
    /// Page-locked host memory: fastest per-proof transfer, never reclaimable.
    Pinned(Vec<BF, A>),
    /// An unlinked mapped file: reclaimable under memory pressure, slower to transfer.
    Mapped(MappedSetupTrace),
}

impl SetupTrace {
    pub fn as_slice(&self) -> &[BF] {
        match self {
            Self::Pinned(vec) => vec.as_slice(),
            Self::Mapped(mapped) => mapped.as_slice(),
        }
    }

    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// True if this trace is file-backed rather than page-locked.
    pub fn is_mapped(&self) -> bool {
        matches!(self, Self::Mapped(_))
    }
}

impl CudaSlice<BF> for SetupTrace {
    unsafe fn as_slice(&self) -> &[BF] {
        SetupTrace::as_slice(self)
    }
}

/// Build a file-backed trace of `elements` and let `fill` write the compact values.
pub fn build_mapped(
    dir: &PathBuf,
    elements: usize,
    fill: impl FnOnce(&mut [BF]),
) -> std::io::Result<MappedSetupTrace> {
    static SEQ: AtomicU64 = AtomicU64::new(0);

    let bytes = elements * size_of::<BF>();
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let mapped_bytes = bytes.next_multiple_of(page);

    std::fs::create_dir_all(dir)?;
    let path = dir.join(format!(
        "airbender-setup-trace-{}-{}.bin",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&path)?;
    // Unlink now: from here the mapping is the only reference, so an abrupt exit cannot
    // leave a multi-gigabyte file behind in the directory.
    let unlink = std::fs::remove_file(&path);
    if let Err(e) = file.set_len(mapped_bytes as u64).and(unlink) {
        return Err(e);
    }

    let ptr = unsafe {
        libc::mmap(
            ptr::null_mut(),
            mapped_bytes,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED,
            file.as_raw_fd(),
            0,
        )
    };
    if ptr == libc::MAP_FAILED {
        return Err(std::io::Error::last_os_error());
    }
    // The mapping holds its own reference to the inode; the descriptor is not needed.
    drop(file);

    let dst = unsafe { slice::from_raw_parts_mut(ptr as *mut BF, elements) };
    fill(dst);

    // Read-only from here: the pages are clean after writeback and so become evictable,
    // and nothing can scribble on a trace that several proofs share.
    if unsafe { libc::mprotect(ptr, mapped_bytes, libc::PROT_READ) } != 0 {
        let err = std::io::Error::last_os_error();
        unsafe { libc::munmap(ptr, mapped_bytes) };
        return Err(err);
    }

    Ok(MappedSetupTrace {
        ptr,
        mapped_bytes,
        len: elements,
    })
}
