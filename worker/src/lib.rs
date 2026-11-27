#![feature(raw_slice_split)]

use std::marker::PhantomData;

use rayon::{ThreadPool, ThreadPoolBuilder};

/// Re-export so `Worker` users can drive its [`ThreadPool`] with rayon's
/// parallel iterators (work stealing) without their own rayon dependency:
/// `worker.pool.install(|| items.par_iter().map(..) .. )`.
pub use rayon;

// We allocate a pool of (ideally) high-performance cores only!
pub struct Worker {
    pub pool: ThreadPool,
    pub num_cores: usize,
}

// For some reason stack size is different in debug/release, and in rust-analyzer and without it, so we enforce it
pub const REQUIRED_STACK_SIZE: usize = 8 * 1024 * 1024;

// the reason for introducing this structure is the following:
/// Work split for a `scope`: `num_chunks` contiguous chunks whose sizes
/// differ by AT MOST ONE — the first `remainder` chunks hold
/// `ordinary_chunk_size + 1` items, the others `ordinary_chunk_size`.
/// (The former rule of dumping the whole remainder into the last chunk gave
/// 256 items on 96 threads as 95 chunks of 2 and one of 66, so a phase
/// waited on a 33x chunk; item counts near the thread count are common at
/// full-socket widths.) Chunk positions come from [`get_chunk_start_pos`] —
/// never from `idx * ordinary_chunk_size`.
#[derive(Clone, Copy, Debug)]
pub struct WorkerGeometry {
    pub num_chunks: usize,
    pub ordinary_chunk_size: usize,
    pub remainder: usize,
}

impl WorkerGeometry {
    /// Balanced chunking: the first `remainder` chunks hold
    /// `ordinary_chunk_size + 1` items, the rest `ordinary_chunk_size`, so
    /// sizes differ by at most one.
    #[inline]
    pub fn get_chunk_size(&self, chunk_idx: usize) -> usize {
        assert!(
            chunk_idx < self.num_chunks,
            "tried to request more chunks than were prepared"
        );
        self.ordinary_chunk_size + (chunk_idx < self.remainder) as usize
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.num_chunks
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.num_chunks == 0
    }

    #[inline]
    pub fn get_chunk_start_pos(&self, chunk_idx: usize) -> usize {
        assert!(
            chunk_idx < self.num_chunks,
            "tried to request more chunks than were prepared"
        );
        self.ordinary_chunk_size * chunk_idx + chunk_idx.min(self.remainder)
    }

    /// Total number of items covered by the geometry.
    #[inline]
    pub fn total_size(&self) -> usize {
        self.ordinary_chunk_size * self.num_chunks + self.remainder
    }
}

pub trait IterableWithGeometry {
    type SliceOver;
    fn chunks_for_geometry(
        &self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunks<'_, Self::SliceOver>;
    fn chunks_for_geometry_with_scale(
        &self,
        geometry: WorkerGeometry,
        scale: usize,
    ) -> GeometryAwareChunks<'_, Self::SliceOver>;
    fn chunks_for_geometry_mut(
        &mut self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunksMut<'_, Self::SliceOver>;
    fn chunks_for_geometry_with_scale_mut(
        &mut self,
        geometry: WorkerGeometry,
        scale: usize,
    ) -> GeometryAwareChunksMut<'_, Self::SliceOver>;
    fn chunks_for_geometry_windows(
        &self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunksCyclicWindow<'_, Self::SliceOver>;
    fn chunks_for_geometry_rev(
        &self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunksRev<'_, Self::SliceOver>;
}

impl<T> IterableWithGeometry for [T] {
    type SliceOver = T;

    #[inline]
    fn chunks_for_geometry(
        &self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunks<'_, Self::SliceOver> {
        GeometryAwareChunks::new(self, geometry, 1)
    }

    #[inline]
    fn chunks_for_geometry_with_scale(
        &self,
        geometry: WorkerGeometry,
        scale: usize,
    ) -> GeometryAwareChunks<'_, Self::SliceOver> {
        GeometryAwareChunks::new(self, geometry, scale)
    }

    #[inline]
    fn chunks_for_geometry_mut(
        &mut self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunksMut<'_, Self::SliceOver> {
        GeometryAwareChunksMut::new(self, geometry, 1)
    }

    #[inline]
    fn chunks_for_geometry_with_scale_mut(
        &mut self,
        geometry: WorkerGeometry,
        scale: usize,
    ) -> GeometryAwareChunksMut<'_, Self::SliceOver> {
        GeometryAwareChunksMut::new(self, geometry, scale)
    }

    #[inline]
    fn chunks_for_geometry_windows(
        &self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunksCyclicWindow<'_, Self::SliceOver> {
        GeometryAwareChunksCyclicWindow::new(self, geometry, 1)
    }

    #[inline]
    fn chunks_for_geometry_rev(
        &self,
        geometry: WorkerGeometry,
    ) -> GeometryAwareChunksRev<'_, Self::SliceOver> {
        GeometryAwareChunksRev::new(self, geometry, 1)
    }
}

#[derive(Debug, Clone)]
pub struct GeometryAwareChunks<'a, T: 'a> {
    v: &'a [T],
    geometry: WorkerGeometry,
    scale: usize,
    cur_idx: usize,
}

impl<'a, T: 'a> GeometryAwareChunks<'a, T> {
    #[inline]
    pub fn new(slice: &'a [T], geometry: WorkerGeometry, scale: usize) -> Self {
        Self {
            v: slice,
            geometry,
            scale,
            cur_idx: 0,
        }
    }

    #[inline]
    pub fn get_cur_chunk_size(&self) -> usize {
        self.geometry.get_chunk_size(self.cur_idx) * self.scale
    }
}

impl<'a, T> Iterator for GeometryAwareChunks<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let chunksz = self.get_cur_chunk_size();
            let (fst, snd) = self.v.split_at(chunksz);
            self.v = snd;
            self.cur_idx += 1;
            Some(fst)
        }
    }
}

#[derive(Debug)]
pub struct GeometryAwareChunksMut<'a, T: 'a> {
    v: *mut [T],
    geometry: WorkerGeometry,
    scale: usize,
    cur_idx: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T: 'a> GeometryAwareChunksMut<'a, T> {
    #[inline]
    pub fn new(slice: &'a mut [T], geometry: WorkerGeometry, scale: usize) -> Self {
        Self {
            v: slice,
            geometry,
            scale,
            cur_idx: 0,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn get_cur_chunk_size(&self) -> usize {
        self.geometry.get_chunk_size(self.cur_idx) * self.scale
    }
}

impl<'a, T> Iterator for GeometryAwareChunksMut<'a, T> {
    type Item = &'a mut [T];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() {
            None
        } else {
            let sz = self.get_cur_chunk_size();
            self.cur_idx += 1;
            // SAFETY: The self.v contract ensures that any split_at_mut is valid.
            let (head, tail) = unsafe { self.v.split_at_mut(sz) };
            self.v = tail;
            // SAFETY: Nothing else points to or will point to the contents of this slice.
            Some(unsafe { &mut *head })
        }
    }
}

#[derive(Debug, Clone)]
pub struct GeometryAwareChunksCyclicWindow<'a, T: 'a> {
    first_elem: &'a T,
    v: &'a [T],
    geometry: WorkerGeometry,
    scale: usize,
    cur_idx: usize,
}

impl<'a, T: 'a> GeometryAwareChunksCyclicWindow<'a, T> {
    #[inline]
    pub fn new(slice: &'a [T], geometry: WorkerGeometry, scale: usize) -> Self {
        Self {
            first_elem: &slice[0],
            v: slice,
            geometry,
            scale,
            cur_idx: 0,
        }
    }

    #[inline]
    pub fn get_cur_chunk_size(&self) -> usize {
        self.geometry.get_chunk_size(self.cur_idx) * self.scale
    }
}

#[derive(Debug, Clone)]
pub struct ChunkExt<'a, T> {
    pub chunk: &'a [T],
    pub next: &'a T,
}

impl<'a, T> ChunkExt<'a, T> {
    pub fn new(chunk: &'a [T], next: &'a T) -> Self {
        ChunkExt { chunk, next }
    }

    pub fn iter(&self) -> impl Iterator<Item = &'a T> {
        self.chunk.iter().chain(std::iter::once(self.next))
    }
}

impl<'a, T> Iterator for GeometryAwareChunksCyclicWindow<'a, T> {
    type Item = ChunkExt<'a, T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.v.is_empty() {
            None
        } else {
            let chunksz = self.get_cur_chunk_size();
            let (fst, snd) = self.v.split_at(chunksz);
            self.v = snd;
            self.cur_idx += 1;
            if self.v.is_empty() {
                Some(ChunkExt::new(fst, self.first_elem))
            } else {
                Some(ChunkExt::new(fst, &self.v[0]))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct GeometryAwareChunksRev<'a, T: 'a> {
    v: &'a [T],
    geometry: WorkerGeometry,
    scale: usize,
    cur_idx: usize,
}

impl<'a, T: 'a> GeometryAwareChunksRev<'a, T> {
    #[inline]
    pub fn new(slice: &'a [T], geometry: WorkerGeometry, scale: usize) -> Self {
        Self {
            v: slice,
            geometry,
            scale,
            cur_idx: geometry.num_chunks - 1,
        }
    }

    #[inline]
    pub fn get_cur_chunk_size(&self) -> usize {
        self.geometry.get_chunk_size(self.cur_idx) * self.scale
    }
}

impl<'a, T> Iterator for GeometryAwareChunksRev<'a, T> {
    type Item = &'a [T];

    #[inline]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() {
            None
        } else {
            let chunksz = self.get_cur_chunk_size();
            let (fst, snd) = self.v.split_at(self.v.len() - chunksz);
            self.v = fst;
            self.cur_idx = self.cur_idx.saturating_sub(1);
            Some(snd)
        }
    }
}

impl Worker {
    /// Workers can be used in context where too much threads can cause overflow,
    /// e.g. in the context of airbender we have several places that assert
    /// `(worker.num_cores as u64) * (trace_len as u64) < (1u64 << 32)` for that
    /// reason. Given that maximum trace length is 2^24, we can pick a safe upper
    /// bound that would be safe to use.
    pub const MAX_WORKER_SIZE: usize = 192;

    pub fn new() -> Self {
        // Bound the builder by the maximum number of threads that is safe to use.
        let num_cores = std::cmp::min(num_cpus::get(), Self::MAX_WORKER_SIZE);

        Self::new_with_num_threads(num_cores)
    }

    pub fn get_num_cores(&self) -> usize {
        self.num_cores
    }

    pub fn new_with_num_threads(num_threads: usize) -> Self {
        assert!(num_threads > 0, "Worker must have at least one thread");
        assert!(
            num_threads <= Self::MAX_WORKER_SIZE,
            "Worker cannot have more than {} threads",
            Self::MAX_WORKER_SIZE
        );

        let pool = ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .stack_size(REQUIRED_STACK_SIZE)
            .build()
            .expect("failed to build thread pool");

        Self {
            pool,
            num_cores: num_threads,
        }
    }

    #[track_caller]
    pub fn get_geometry(&self, work_size: usize) -> WorkerGeometry {
        Self::get_geometry_for_num_cores(self.num_cores, work_size)
    }

    #[track_caller]
    pub fn get_geometry_for_num_cores(num_cores: usize, work_size: usize) -> WorkerGeometry {
        if num_cores == 0 {
            panic!("No cores to work with");
        }
        if work_size == 0 {
            panic!("Empty work");
        }
        // every chunk gets at least one item; sizes differ by at most one
        let num_chunks = std::cmp::min(num_cores, work_size);
        WorkerGeometry {
            num_chunks,
            ordinary_chunk_size: work_size / num_chunks,
            remainder: work_size % num_chunks,
        }
    }

    #[track_caller]
    pub fn scope<'a, F, R>(&self, work_size: usize, f: F) -> R
    where
        F: FnOnce(&rayon::Scope<'a>, WorkerGeometry) -> R,
    {
        let work_geometry = self.get_geometry(work_size);
        self.pool.in_place_scope(|scope| f(scope, work_geometry))
    }

    /// Like [`scope`], but returns a single-chunk geometry when `work_size < threshold`,
    /// causing `smart_spawn` to run the body on the calling thread with no spawning overhead.
    #[track_caller]
    pub fn scope_with_threshold<'a, F, R>(&self, work_size: usize, threshold: usize, f: F) -> R
    where
        F: FnOnce(&rayon::Scope<'a>, WorkerGeometry) -> R,
    {
        let work_geometry = self.get_geometry_with_threshold(work_size, threshold);
        self.pool.in_place_scope(|scope| f(scope, work_geometry))
    }

    /// Returns a single-chunk geometry when `work_size < threshold`; otherwise behaves
    /// identically to [`get_geometry`].
    #[track_caller]
    pub fn get_geometry_with_threshold(
        &self,
        work_size: usize,
        threshold: usize,
    ) -> WorkerGeometry {
        if work_size < threshold {
            WorkerGeometry {
                num_chunks: 1,
                ordinary_chunk_size: work_size,
                remainder: 0,
            }
        } else {
            self.get_geometry(work_size)
        }
    }

    pub fn smart_spawn<'scope, BODY>(scope: &rayon::Scope<'scope>, is_last_thread: bool, body: BODY)
    where
        BODY: FnOnce(&rayon::Scope<'scope>) + Send + 'scope,
    {
        if !is_last_thread {
            scope.spawn(body);
        } else {
            body(scope);
        }
    }
}

impl Default for Worker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod geometry_tests {
    use super::*;

    #[test]
    fn chunks_are_balanced_contiguous_and_complete() {
        for &(cores, work) in &[
            (1usize, 1usize),
            (1, 1000),
            (96, 5),
            (96, 96),
            (96, 97),
            (96, 191),
            (96, 256),
            (96, 1000),
            (96, 65536),
            (192, 256),
            (7, 100),
            (8, 100),
            (3, 2),
        ] {
            let g = Worker::get_geometry_for_num_cores(cores, work);
            assert_eq!(g.len(), cores.min(work), "{cores} cores, {work} items");
            assert_eq!(g.total_size(), work);
            let mut pos = 0;
            let (mut min, mut max) = (usize::MAX, 0);
            for i in 0..g.len() {
                assert_eq!(g.get_chunk_start_pos(i), pos, "chunk {i} of {cores}/{work}");
                let size = g.get_chunk_size(i);
                assert!(size >= 1);
                min = min.min(size);
                max = max.max(size);
                pos += size;
            }
            assert_eq!(pos, work);
            assert!(
                max - min <= 1,
                "{cores} cores, {work} items: sizes {min}..{max}"
            );
            // iterators agree with the accessors
            let data: Vec<usize> = (0..work).collect();
            let fwd: Vec<&[usize]> = data.chunks_for_geometry(g).collect();
            assert_eq!(fwd.len(), g.len());
            for (i, c) in fwd.iter().enumerate() {
                assert_eq!(c.len(), g.get_chunk_size(i));
                assert_eq!(c[0], g.get_chunk_start_pos(i));
            }
            let rev: Vec<&[usize]> = data.chunks_for_geometry_rev(g).collect();
            assert_eq!(rev.len(), g.len());
            for (k, c) in rev.iter().enumerate() {
                let i = g.len() - 1 - k;
                assert_eq!(c.len(), g.get_chunk_size(i));
                assert_eq!(c[0], g.get_chunk_start_pos(i));
            }
        }
    }
}
