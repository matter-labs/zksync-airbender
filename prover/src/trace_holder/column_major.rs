use super::*;

#[derive(Debug)]
pub struct ColumnMajorTrace<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone> {
    pub ptr: *mut T,
    num_columns: usize,
    length: usize,
    allocator: A,
}

unsafe impl<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone> Send
    for ColumnMajorTrace<T, A>
{
}
unsafe impl<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone> Sync
    for ColumnMajorTrace<T, A>
{
}

unsafe impl<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone>
    ColumnMajorTraceStorage<T> for ColumnMajorTrace<T, A>
{
    fn start(&self) -> SendSyncPtrWrapper<T> {
        SendSyncPtrWrapper(self.ptr)
    }

    fn width(&self) -> usize {
        self.num_columns
    }

    fn len(&self) -> usize {
        self.length
    }
}

impl<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone> Drop
    for ColumnMajorTrace<T, A>
{
    fn drop(&mut self) {
        unsafe {
            let required_size = self.length * self.num_columns * core::mem::size_of::<T>();
            let full_capacity = required_size.next_multiple_of(PAGE_SIZE);
            let reconstructed_capacity = Vec::<u8, A>::from_raw_parts_in(
                self.ptr.cast(),
                full_capacity,
                full_capacity,
                self.allocator.clone(),
            );
            drop(reconstructed_capacity);
        }
    }
}

impl<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone> Clone
    for ColumnMajorTrace<T, A>
{
    fn clone(&self) -> Self {
        let new = Self::new_uninit_for_size(self.length, self.num_columns, self.allocator());
        // memcopy
        let num_elements = self.num_columns * self.length;
        unsafe { core::ptr::copy_nonoverlapping(self.ptr.cast_const(), new.ptr, num_elements) }

        new
    }

    fn clone_from(&mut self, source: &Self) {
        assert_eq!(self.length, source.length);
        assert_eq!(self.num_columns, source.num_columns);
        let num_elements = self.num_columns * self.length;
        unsafe { core::ptr::copy_nonoverlapping(source.ptr.cast_const(), self.ptr, num_elements) }
    }
}

impl<T: 'static + Sized + Send + Sync + Clone + Copy, A: Allocator + Clone> ColumnMajorTrace<T, A> {
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            core::slice::from_raw_parts(self.ptr.cast_const(), self.length * self.num_columns)
        }
    }
    pub fn len(&self) -> usize {
        self.length
    }

    pub fn width(&self) -> usize {
        self.num_columns
    }

    pub fn allocator(&self) -> A {
        self.allocator.clone()
    }

    pub fn new_uninit_for_size(rows: usize, columns: usize, allocator: A) -> Self {
        assert!(rows.is_power_of_two());
        let required_size = columns * rows * std::mem::size_of::<T>();
        let num_elements = required_size.next_multiple_of(PAGE_SIZE) / PAGE_SIZE;
        let capacity = Vec::<Aligner, A>::with_capacity_in(num_elements, allocator);
        let (ptr, _, _, alloc) = capacity.into_raw_parts_with_alloc();

        Self {
            ptr: ptr.cast(),
            num_columns: columns,
            length: rows,
            allocator: alloc,
        }
    }

    #[track_caller]
    pub fn columns_iter(&'_ self) -> impl Iterator<Item = &'_ [T]> {
        unsafe {
            let mut column_idx = 0;
            let num_columns = self.num_columns;
            let start_ptr = self.ptr;
            let length = self.length;
            core::iter::from_fn(move || {
                if column_idx < num_columns {
                    let ptr = start_ptr.add(length * column_idx);
                    column_idx += 1;

                    Some(core::slice::from_raw_parts(ptr.cast_const(), length))
                } else {
                    None
                }
            })
        }
    }

    #[track_caller]
    pub fn columns_iter_mut(&'_ mut self) -> impl Iterator<Item = &'_ mut [T]> {
        unsafe {
            let mut column_idx = 0;
            let num_columns = self.num_columns;
            let start_ptr = self.ptr;
            let length = self.length;
            core::iter::from_fn(move || {
                if column_idx < num_columns {
                    let ptr = start_ptr.add(length * column_idx);
                    column_idx += 1;

                    Some(core::slice::from_raw_parts_mut(ptr, length))
                } else {
                    None
                }
            })
        }
    }
}

impl<T: 'static + Sized + Send + Sync + Clone + Copy + Zeroable, A: Allocator + Clone>
    ColumnMajorTrace<T, A>
{
    pub fn new_zeroed_for_size(rows: usize, columns: usize, allocator: A) -> Self {
        let new = Self::new_uninit_for_size(rows, columns, allocator);
        unsafe {
            let start = new.ptr.cast::<u8>();
            core::ptr::write_bytes(
                start,
                0u8,
                new.length * new.num_columns * std::mem::size_of::<T>(),
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
        let new = Self::new_uninit_for_size(rows, columns, allocator);
        let new_ref = &new;
        let num_bytes = new.length * new.num_columns * std::mem::size_of::<T>();

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
