use std::any::type_name;

use super::*;

pub struct RowMajorTrace<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone> {
    pub ptr: *mut T,
    width: usize,
    length: usize,
    pub padded_width: usize,
    allocator: A,
}

impl<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone> std::fmt::Debug
    for RowMajorTrace<T, N, A>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(&format!(
            "RowMajorTrace::<{}, {}, {}>",
            type_name::<T>(),
            N,
            type_name::<A>()
        ))
        .field("width", &self.width)
        .field("length", &self.length)
        .field("padded width", &self.padded_width)
        .finish()
    }
}

unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone> Send
    for RowMajorTrace<T, N, A>
{
}
unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone> Sync
    for RowMajorTrace<T, N, A>
{
}

impl<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone> Drop
    for RowMajorTrace<T, N, A>
{
    fn drop(&mut self) {
        unsafe {
            let required_size = self.length * self.padded_width * core::mem::size_of::<T>();
            let full_capacity = required_size.next_multiple_of(PAGE_SIZE) / PAGE_SIZE;
            let slice = std::slice::from_raw_parts_mut(self.ptr.cast(), full_capacity);
            if crate::VERBOSE {
                println!(
                    "Will deallocate trace holder at range {:?}",
                    slice.as_ptr_range()
                );
            }
            let reconstructed_capacity =
                Box::<[Aligner], A>::from_raw_in(slice as *mut [Aligner], self.allocator.clone());
            assert_eq!(reconstructed_capacity.len(), full_capacity);
            drop(reconstructed_capacity);
        }
    }
}

impl<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone> Clone
    for RowMajorTrace<T, N, A>
{
    fn clone(&self) -> Self {
        let new = Self::new_uninit_for_size(self.length, self.width, self.allocator());
        assert_eq!(self.length, new.length);
        assert_eq!(self.padded_width, new.padded_width);
        assert_eq!(self.width, new.width);
        // memcopy
        let num_elements = self.padded_width * self.length;
        unsafe {
            core::ptr::copy_nonoverlapping(self.ptr.cast_const(), new.ptr, num_elements);
        }

        new
    }

    fn clone_from(&mut self, source: &Self) {
        assert_eq!(self.length, source.length);
        assert_eq!(self.padded_width, source.padded_width);
        assert_eq!(self.width, source.width);
        let num_elements = self.padded_width * self.length;
        unsafe {
            core::ptr::copy_nonoverlapping(source.ptr.cast_const(), self.ptr, num_elements);
        }
    }
}

impl<T: 'static + Sized + Clone + Copy, const N: usize, A: Allocator + Clone>
    RowMajorTrace<T, N, A>
{
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            core::slice::from_raw_parts(self.ptr.cast_const(), self.length * self.padded_width)
        }
    }
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr, self.length * self.padded_width) }
    }
    pub fn len(&self) -> usize {
        self.length
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn allocator(&self) -> A {
        self.allocator.clone()
    }

    pub fn num_column_chunks(&self, width: usize) -> usize {
        assert!(width.is_power_of_two());
        assert!(self.padded_width % width == 0);

        self.padded_width / width
    }

    pub fn new_uninit_for_size(rows: usize, columns: usize, allocator: A) -> Self {
        assert!(N.is_power_of_two());
        let padded_columns = columns.next_multiple_of(N);
        let required_size = padded_columns * rows * std::mem::size_of::<T>();
        let num_elements = required_size.next_multiple_of(PAGE_SIZE) / PAGE_SIZE;
        assert_eq!(std::mem::size_of::<Aligner>(), PAGE_SIZE);
        assert_eq!(std::mem::align_of::<Aligner>(), PAGE_SIZE);
        let capacity = unsafe {
            Box::<[Aligner], A>::new_uninit_slice_in(num_elements, allocator).assume_init()
        };
        assert_eq!(capacity.len(), num_elements);
        if crate::VERBOSE {
            println!(
                "Trace holder was allocated at range {:?}",
                capacity.as_ptr_range()
            );
        }
        let (ptr, alloc) = Box::into_raw_with_allocator(capacity);

        Self {
            ptr: ptr.cast(),
            width: columns,
            length: rows,
            padded_width: padded_columns,
            allocator: alloc,
        }
    }

    #[track_caller]
    pub fn row_view_subtrace(&self, range: std::ops::Range<usize>) -> Self {
        assert!(range.end <= self.length);
        let length = range.len();

        let ptr = unsafe { self.ptr.add(self.padded_width * range.start) };

        Self {
            ptr,
            padded_width: self.padded_width,
            width: self.width,
            length,
            allocator: self.allocator.clone(),
        }
    }

    #[track_caller]
    pub fn row_view(&self, range: std::ops::Range<usize>) -> RowMajorTraceView<T, N> {
        assert!(range.end <= self.length);
        let length = range.len();

        let ptr = unsafe { self.ptr.add(self.padded_width * range.start) };

        RowMajorTraceView {
            ptr,
            padded_width: self.padded_width,
            width: self.width,
            length,
            full_trace_starting_ptr: self.ptr,
            full_trace_ending_ptr: unsafe { self.ptr.add(self.padded_width * self.length) },
        }
    }

    #[track_caller]
    pub fn column_view(&self, offset: usize, width: usize) -> RowMajorTraceColumnsView<T, N> {
        assert!(width > 0);
        assert!(
            width + offset <= self.padded_width,
            "trace has padded width {}, but caller requested {} columns at offset {}",
            self.padded_width,
            width,
            offset
        );

        let ptr = unsafe { self.ptr.add(offset) };

        RowMajorTraceColumnsView {
            ptr,
            viewed_width: width,
            offset_per_row: self.padded_width,
            length: self.length,
        }
    }

    pub fn tile_view(
        &self,
        rows: std::ops::Range<usize>,
        width: usize,
        offset: usize,
    ) -> RowMajorTraceColumnsView<T, N> {
        assert!(rows.end <= self.length);
        let length = rows.len();
        assert!(width * (offset + 1) <= self.padded_width);

        let ptr = unsafe { self.ptr.add(self.padded_width * rows.start) };
        let ptr = unsafe { ptr.add(width * offset) };

        RowMajorTraceColumnsView {
            ptr,
            viewed_width: width,
            offset_per_row: self.padded_width,
            length: length,
        }
    }

    #[track_caller]
    pub fn column_view_fixed<const M: usize>(
        &self,
        offset: usize,
    ) -> RowMajorTraceFixedColumnsView<T, N, M> {
        assert!(M.is_power_of_two());
        assert!(
            M * (offset + 1) <= self.padded_width,
            "trying to get offset {} for column view of width {}, but our padded width is {}",
            offset,
            M,
            self.padded_width
        );

        let ptr = unsafe { self.ptr.add(M * offset) };

        RowMajorTraceFixedColumnsView {
            ptr,
            offset_per_row: self.padded_width,
            length: self.length,
        }
    }

    #[inline(always)]
    pub unsafe fn get_row(&self, row_index: usize) -> &[T] {
        debug_assert!(row_index < self.length);

        core::slice::from_raw_parts(self.ptr.add(self.padded_width * row_index), self.width)
    }

    #[inline(always)]
    pub fn get_row_mut(&mut self, row_index: usize) -> &mut [T] {
        debug_assert!(row_index < self.length);
        unsafe {
            let ptr = self.ptr.add(self.padded_width * row_index);
            core::slice::from_raw_parts_mut(ptr, self.width)
        }
    }

    pub fn clone_parallel(&self, worker: &Worker) -> Self {
        let new_trace =
            RowMajorTrace::new_uninit_for_size(self.len(), self.width(), self.allocator());

        let trace_ref = &self;
        let new_trace_ref = &new_trace;
        worker.scope(trace_ref.len(), |scope, geometry| {
            for thread_idx in 0..worker.num_cores {
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let end = start + chunk_size;
                    let trace_view = trace_ref.row_view(start..end);
                    let mut new_trace_view = new_trace_ref.row_view(start..end);
                    unsafe {
                        core::ptr::copy_nonoverlapping(
                            trace_view.current_row_ref().as_ptr(),
                            new_trace_view.current_row().as_mut_ptr(),
                            chunk_size * trace_ref.padded_width,
                        )
                    }
                });
            }
        });
        new_trace
    }
}

impl<T: 'static + Sized + Clone + Copy + Zeroable, const N: usize, A: Allocator + Clone>
    RowMajorTrace<T, N, A>
{
    pub fn new_zeroed_for_size(rows: usize, columns: usize, allocator: A) -> Self {
        let new = Self::new_uninit_for_size(rows, columns, allocator);
        unsafe {
            let start = new.ptr.cast::<u8>();
            core::ptr::write_bytes(
                start,
                0u8,
                new.length * new.padded_width * std::mem::size_of::<T>(),
            );
        }

        new
    }

    pub fn new_zeroed_for_size_parallel(
        rows: usize,
        columns: usize,
        allocator: A,
        worker: &Worker,
    ) -> Self {
        if rows == 0 || columns == 0 {
            return Self::new_zeroed_for_size(rows, columns, allocator);
        }
        let new = Self::new_uninit_for_size(rows, columns, allocator);
        let new_ref = &new;
        let num_bytes = new.length * new.padded_width * std::mem::size_of::<T>();

        worker.scope(num_bytes, |scope, geometry| {
            for thread_idx in 0..worker.num_cores {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    let start = new_ref.ptr.cast::<u8>().add(chunk_start);
                    core::ptr::write_bytes(start, 0u8, chunk_size);
                });
            }
        });

        new
    }
}

#[derive(Clone)]
pub struct RowMajorTraceView<T: 'static + Sized + Clone + Copy, const N: usize> {
    ptr: *mut T,
    width: usize,
    length: usize,
    padded_width: usize,
    full_trace_starting_ptr: *const T,
    full_trace_ending_ptr: *const T,
}

unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize> Send for RowMajorTraceView<T, N> {}
unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize> Sync for RowMajorTraceView<T, N> {}

impl<T: 'static + Sized + Clone + Copy, const N: usize> RowMajorTraceView<T, N> {
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.length
    }

    #[inline(always)]
    pub fn width(&self) -> usize {
        self.width
    }

    #[inline(always)]
    pub fn padded_width(&self) -> usize {
        self.padded_width
    }

    #[inline(always)]
    pub fn current_row_ref(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.ptr.cast_const(), self.width) }
    }

    #[inline(always)]
    pub fn current_and_next_row_ref(&self) -> (&[T], &[T]) {
        unsafe {
            let this_row_ptr = self.ptr.cast_const();
            let mut next_row_ptr = this_row_ptr.add(self.padded_width);
            if next_row_ptr >= self.full_trace_ending_ptr {
                next_row_ptr = self.full_trace_starting_ptr;
            }
            (
                core::slice::from_raw_parts(this_row_ptr, self.width),
                core::slice::from_raw_parts(next_row_ptr, self.width),
            )
        }
    }

    #[inline(always)]
    pub fn current_and_previous_row_ref(&self) -> (&[T], &[T]) {
        unsafe {
            let this_row_ptr = self.ptr.cast_const();
            let previous_row_ptr = if this_row_ptr == self.full_trace_starting_ptr {
                self.full_trace_ending_ptr.sub(self.padded_width)
            } else {
                this_row_ptr.sub(self.padded_width)
            };
            (
                core::slice::from_raw_parts(this_row_ptr, self.width),
                core::slice::from_raw_parts(previous_row_ptr, self.width),
            )
        }
    }

    #[inline(always)]
    pub fn current_row(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr, self.width) }
    }

    #[inline(always)]
    pub unsafe fn current_row_split(&mut self, mid: usize) -> (&mut [T], &mut [T]) {
        // SAFETY: mid should be less than width
        (
            core::slice::from_raw_parts_mut(self.ptr, mid),
            core::slice::from_raw_parts_mut(self.ptr.add(mid), self.width - mid),
        )
    }

    #[inline(always)]
    pub fn current_row_padded(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr, self.padded_width) }
    }

    #[inline(always)]
    pub fn advance_row(&mut self) {
        let offset = self.padded_width;
        self.length -= 1;
        unsafe {
            self.ptr = self.ptr.add(offset);
        }
    }

    #[track_caller]
    pub fn row_view(&self, range: std::ops::Range<usize>) -> Self {
        assert!(range.end <= self.length);
        let length = range.len();

        let ptr = unsafe { self.ptr.add(self.padded_width * range.start) };

        Self {
            ptr,
            padded_width: self.padded_width,
            width: self.width,
            length,
            full_trace_starting_ptr: self.ptr,
            full_trace_ending_ptr: unsafe { self.ptr.add(self.padded_width * self.length) },
        }
    }

    #[inline(always)]
    pub unsafe fn get_row(&self, row_index: usize) -> &[T] {
        debug_assert!(row_index < self.length);

        core::slice::from_raw_parts(self.ptr.add(self.padded_width * row_index), self.width)
    }

    #[inline(always)]
    pub fn get_row_mut(&mut self, row_index: usize) -> &mut [T] {
        debug_assert!(row_index < self.length);
        unsafe {
            let ptr = self.ptr.add(self.padded_width * row_index);
            core::slice::from_raw_parts_mut(ptr, self.width)
        }
    }

    #[inline(always)]
    pub fn get_row_mut_vectorized(
        &self,
        row_index: usize,
    ) -> &mut [Mersenne31ComplexVectorizedInterleaved] {
        debug_assert!(row_index < self.length);
        unsafe {
            let ptr = self.ptr.add(self.padded_width * row_index);
            let row = core::slice::from_raw_parts_mut(ptr, self.padded_width);
            cast_check_alignment_ref_mut_pack::<T, Mersenne31ComplexVectorizedInterleaved>(row)
        }
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe {
            core::slice::from_raw_parts(self.ptr.cast_const(), self.length * self.padded_width)
        }
    }
}

pub struct RowMajorTraceColumnsView<T: 'static + Sized + Clone + Copy, const N: usize> {
    ptr: *mut T,
    offset_per_row: usize,
    viewed_width: usize,
    length: usize,
}

unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize> Send
    for RowMajorTraceColumnsView<T, N>
{
}
unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize> Sync
    for RowMajorTraceColumnsView<T, N>
{
}

impl<T: 'static + Sized + Clone + Copy, const N: usize> RowMajorTraceColumnsView<T, N> {
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.length
    }

    #[inline(always)]
    pub fn width(&self) -> usize {
        self.viewed_width
    }

    #[inline(always)]
    pub fn current_row(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.ptr.cast_const(), self.viewed_width) }
    }

    #[inline(always)]
    pub fn get_row(&self, idx: usize) -> &[T] {
        debug_assert!(idx < self.length);
        unsafe {
            let ptr = self.ptr.add(self.offset_per_row * idx);
            core::slice::from_raw_parts(ptr.cast_const(), self.viewed_width)
        }
    }

    #[inline(always)]
    pub fn get_row_mut(&mut self, idx: usize) -> &mut [T] {
        debug_assert!(idx < self.length);
        unsafe {
            let ptr = self.ptr.add(self.offset_per_row * idx);
            core::slice::from_raw_parts_mut(ptr, self.viewed_width)
        }
    }

    #[inline(always)]
    pub fn advance_row(&mut self) {
        unsafe {
            self.ptr = self.ptr.add(self.offset_per_row);
        }
    }

    #[inline(always)]
    pub fn advance_many(&mut self, offset: usize) {
        unsafe {
            self.ptr = self.ptr.add(self.offset_per_row * offset);
        }
    }
}

pub struct RowMajorTraceFixedColumnsView<
    T: 'static + Sized + Clone + Copy,
    const N: usize,
    const M: usize,
> {
    ptr: *mut T,
    offset_per_row: usize,
    length: usize,
}

unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize, const M: usize> Send
    for RowMajorTraceFixedColumnsView<T, N, M>
{
}
unsafe impl<T: 'static + Sized + Clone + Copy, const N: usize, const M: usize> Sync
    for RowMajorTraceFixedColumnsView<T, N, M>
{
}

impl<T: 'static + Sized + Clone + Copy, const N: usize, const M: usize>
    RowMajorTraceFixedColumnsView<T, N, M>
{
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.length
    }

    #[inline(always)]
    pub fn current_row(&mut self) -> &mut [T; M] {
        unsafe { &mut *self.ptr.cast::<[T; M]>() }
    }

    #[inline(always)]
    pub fn get_row(&self, idx: usize) -> &[T; M] {
        debug_assert!(idx < self.length);
        unsafe {
            let ptr = self.ptr.add(self.offset_per_row * idx);
            &*ptr.cast_const().cast::<[T; M]>()
        }
    }

    #[inline(always)]
    pub fn get_row_mut(&mut self, idx: usize) -> &mut [T; M] {
        debug_assert!(idx < self.length);
        unsafe {
            let ptr = self.ptr.add(self.offset_per_row * idx);
            &mut *ptr.cast::<[T; M]>()
        }
    }

    #[inline(always)]
    pub fn advance_row(&mut self) {
        unsafe {
            self.ptr = self.ptr.add(self.offset_per_row);
        }
    }

    #[inline(always)]
    pub fn get_slice(&self, slice_start: usize, slice_end: usize) -> Self {
        assert!(slice_end <= self.length);
        assert!(slice_start < slice_end);
        let slice_ptr = unsafe { self.ptr.add(self.offset_per_row * slice_start) };
        Self {
            ptr: slice_ptr,
            offset_per_row: self.offset_per_row,
            length: slice_end - slice_start,
        }
    }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use field::Field;

    use super::*;

    #[test]
    fn test_zero_out() {
        let new =
            RowMajorTrace::<Mersenne31Field, 32, Global>::new_zeroed_for_size(1 << 20, 300, Global);
        for el in new.as_slice().iter() {
            assert!(el.is_zero());
        }
    }

    #[test]
    fn test_clone() {
        let mut initial =
            RowMajorTrace::<Mersenne31Field, 32, Global>::new_zeroed_for_size(1 << 20, 300, Global);
        for (i, dst) in initial.as_slice_mut().iter_mut().enumerate() {
            *dst = Mersenne31Field::from_nonreduced_u32((i % (1 << 32)) as u32);
        }
        let cloned = initial.clone();
        assert_eq!(initial.as_slice(), cloned.as_slice());
    }
}
