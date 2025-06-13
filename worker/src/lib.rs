#![feature(raw_slice_split)]

use std::marker::PhantomData;

use rayon::{ThreadPool, ThreadPoolBuilder};

// We allocate a pool of (ideally) high-performance cores only!
pub struct Worker {
    pub pool: ThreadPool,
    pub num_cores: usize,
}

// For some reason stack size is different in debug/release, and in rust-analyzer and without it, so we enforce it
pub const REQUIRED_STACK_SIZE: usize = 8 * 1024 * 1024;

// the reason for introducing this structure is the following:
// nobody could guarantee us that the total number of jobs is divisible by number_of_cores without remainder
// e.g. if num_jobs = 16 and num_cores = 3 the best way of splitting the work among the threads is the following:
// rem = 16 / 3 = 1; quotient = 16/ 3 = 5 => the first thread then executes 6 operations and remaining threads 5
// basically remainder is the number of threads which do ordinary_chunks + 1 operations
// we also want all the chunks to be continuous memory, so don't use chunks.remainder
#[derive(Debug, Clone, Copy)]
pub struct WorkerGeometry {
    pub num_chunks: usize,
    pub ordinary_chunk_size: usize,
    pub remainder: usize,
}

impl WorkerGeometry {
    #[inline]
    pub fn get_chunk_size(&self, chunk_idx: usize) -> usize {
        assert!(
            chunk_idx < self.num_chunks,
            "tried to request more chunks than were prepared"
        );
        if self.remainder == 0 {
            self.ordinary_chunk_size
        } else {
            if chunk_idx == self.num_chunks - 1 {
                // last one
                self.remainder
            } else {
                self.ordinary_chunk_size
            }
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.num_chunks
    }

    #[inline]
    pub fn get_chunk_start_pos(&self, chunk_idx: usize) -> usize {
        assert!(
            chunk_idx < self.num_chunks,
            "tried to request more chunks than were prepared"
        );
        self.ordinary_chunk_size * chunk_idx
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
            cur_idx: slice.len() - 1,
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
            self.cur_idx += 1;
            Some(snd)
        }
    }
}

impl Worker {
    pub fn new() -> Self {
        let num_cores = num_cpus::get();

        Self::new_with_num_threads(num_cores)
    }

    pub fn get_num_cores(&self) -> usize {
        self.num_cores
    }

    pub fn new_with_num_threads(num_threads: usize) -> Self {
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

    pub fn get_geometry(&self, work_size: usize) -> WorkerGeometry {
        Self::get_geometry_for_num_cores(self.num_cores, work_size)
    }

    pub fn get_geometry_for_num_cores(num_cores: usize, work_size: usize) -> WorkerGeometry {
        // we should ensure that ebery thread has at least some work to do
        let num_chunks = std::cmp::min(num_cores, work_size);

        let mut ordinary_chunk_size = work_size / num_chunks;
        let remainder = work_size % num_chunks;
        let mut result = if remainder == 0 {
            // we will have equal work for each of the threads
            WorkerGeometry {
                num_chunks,
                ordinary_chunk_size,
                remainder,
            }
        } else {
            assert!(num_chunks > 1);
            // we will first try simple heuristics, and if it doesn't work - then degrade to default
            if ordinary_chunk_size.is_power_of_two() == false {
                let difference = ordinary_chunk_size.next_power_of_two() - ordinary_chunk_size;
                if difference < 32 {
                    ordinary_chunk_size = ordinary_chunk_size.next_power_of_two();
                }
            }

            let main_part = (num_chunks - 1) * ordinary_chunk_size;
            if main_part < work_size {
                let new_remainder = work_size - main_part;

                WorkerGeometry {
                    num_chunks,
                    ordinary_chunk_size,
                    remainder: new_remainder,
                }
            } else {
                if work_size % (num_chunks - 1) != 0 {
                    ordinary_chunk_size = work_size / (num_chunks - 1);
                    let main_part = (num_chunks - 1) * ordinary_chunk_size;
                    assert!(main_part < work_size);
                    let new_remainder = work_size - main_part;

                    WorkerGeometry {
                        num_chunks,
                        ordinary_chunk_size,
                        remainder: new_remainder,
                    }
                } else {
                    ordinary_chunk_size = work_size / num_chunks;
                    let main_part = (num_chunks - 1) * ordinary_chunk_size;
                    assert!(main_part < work_size);
                    let new_remainder = work_size - main_part;

                    WorkerGeometry {
                        num_chunks,
                        ordinary_chunk_size,
                        remainder: new_remainder,
                    }
                }
            }
        };

        // We want to make the last chunk the smallest one if possible
        if result.remainder > result.ordinary_chunk_size && result.remainder > num_cores - 1 {
            result.remainder -= num_cores - 1;
            result.ordinary_chunk_size += 1;

            assert!(result.ordinary_chunk_size > result.remainder);
        }

        result
    }

    pub fn scope<'a, F, R>(&self, work_size: usize, f: F) -> R
    where
        F: FnOnce(&rayon::Scope<'a>, WorkerGeometry) -> R,
    {
        let work_geometry = self.get_geometry(work_size);
        self.pool.in_place_scope(|scope| f(scope, work_geometry))
    }

    pub fn smart_spawn<'scope, BODY>(scope: &rayon::Scope<'scope>, is_last_thread: bool, body: BODY)
    where
        BODY: FnOnce(&rayon::Scope<'scope>) + Send + 'scope,
    {
        if is_last_thread == false {
            scope.spawn(body);
        } else {
            body(scope);
        }
    }
}
