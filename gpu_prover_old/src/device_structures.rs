use era_cudart::memory::DeviceAllocation;
use era_cudart::memory_pools::DevicePoolAllocation;
use era_cudart::slice::{DeviceSlice, DeviceVariable};

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct PtrAndStride<T> {
    pub ptr: *const T,
    pub stride: usize,
}

impl<T> PtrAndStride<T> {
    pub fn new(ptr: *const T, stride: usize) -> Self {
        Self { ptr, stride }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct MutPtrAndStride<T> {
    pub ptr: *mut T,
    pub stride: usize,
}

impl<T> MutPtrAndStride<T> {
    pub fn new(ptr: *mut T, stride: usize) -> Self {
        Self { ptr, stride }
    }
}

fn ptr_from_slice_and_offset<T>(slice: &DeviceSlice<T>, offset: usize) -> *const T {
    unsafe { slice.as_ptr().add(offset) }
}

fn mut_ptr_from_slice_and_offset<T>(slice: &mut DeviceSlice<T>, offset: usize) -> *mut T {
    unsafe { slice.as_mut_ptr().add(offset) }
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct PtrAndStrideWrappingMatrix<T> {
    pub ptr_and_stride: PtrAndStride<T>,
    pub rows: u32,
    pub cols: u32,
}

impl<T> PtrAndStrideWrappingMatrix<T> {
    pub fn new(matrix: &(impl DeviceMatrixChunkImpl<T> + ?Sized)) -> Self {
        assert!(matrix.rows() <= u32::MAX as usize);
        assert!(matrix.cols() <= u32::MAX as usize);
        Self {
            ptr_and_stride: matrix.as_ptr_and_stride(),
            rows: matrix.rows() as u32,
            cols: matrix.cols() as u32,
        }
    }
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct MutPtrAndStrideWrappingMatrix<T> {
    pub mut_ptr_and_stride: MutPtrAndStride<T>,
    pub rows: u32,
    pub cols: u32,
}

impl<T> MutPtrAndStrideWrappingMatrix<T> {
    pub fn new(matrix: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized)) -> Self {
        assert!(matrix.rows() <= u32::MAX as usize);
        assert!(matrix.cols() <= u32::MAX as usize);
        Self {
            mut_ptr_and_stride: matrix.as_mut_ptr_and_stride(),
            rows: matrix.rows() as u32,
            cols: matrix.cols() as u32,
        }
    }
}

pub trait DeviceVectorImpl<T> {
    fn slice(&self) -> &DeviceSlice<T>;

    fn as_ptr(&self) -> *const T {
        self.slice().as_ptr()
    }

    fn as_ptr_and_stride(&self) -> PtrAndStride<T> {
        PtrAndStride::new(self.as_ptr(), self.slice().len())
    }
}

pub trait DeviceVectorMutImpl<T>: DeviceVectorImpl<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T>;

    fn as_mut_ptr(&mut self) -> *mut T {
        self.slice_mut().as_mut_ptr()
    }

    fn as_mut_ptr_and_stride(&mut self) -> MutPtrAndStride<T> {
        MutPtrAndStride::new(self.as_mut_ptr(), self.slice().len())
    }
}

pub trait DeviceVectorChunkImpl<T> {
    fn slice(&self) -> &DeviceSlice<T>;

    fn offset(&self) -> usize {
        0
    }

    fn rows(&self) -> usize {
        self.slice().len()
    }

    fn as_ptr(&self) -> *const T {
        ptr_from_slice_and_offset(self.slice(), self.offset())
    }

    fn as_ptr_and_stride(&self) -> PtrAndStride<T> {
        PtrAndStride::new(self.as_ptr(), self.slice().len())
    }
}

pub trait DeviceVectorChunkMutImpl<T>: DeviceVectorChunkImpl<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T>;

    fn as_mut_ptr(&mut self) -> *mut T {
        let offset = self.offset();
        mut_ptr_from_slice_and_offset(self.slice_mut(), offset)
    }

    fn as_mut_ptr_and_stride(&mut self) -> MutPtrAndStride<T> {
        MutPtrAndStride::new(self.as_mut_ptr(), self.slice().len())
    }
}

pub trait DeviceMatrixImpl<T> {
    fn slice(&self) -> &DeviceSlice<T>;

    fn stride(&self) -> usize {
        self.slice().len()
    }

    fn cols(&self) -> usize {
        self.slice().len() / self.stride()
    }

    fn as_ptr(&self) -> *const T {
        self.slice().as_ptr()
    }

    fn as_ptr_and_stride(&self) -> PtrAndStride<T> {
        PtrAndStride::new(self.as_ptr(), self.stride())
    }
}

pub trait DeviceMatrixMutImpl<T>: DeviceMatrixImpl<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T>;

    fn as_mut_ptr(&mut self) -> *mut T {
        self.slice_mut().as_mut_ptr()
    }

    fn as_mut_ptr_and_stride(&mut self) -> MutPtrAndStride<T> {
        MutPtrAndStride::new(self.as_mut_ptr(), self.stride())
    }
}

pub trait DeviceMatrixChunkImpl<T> {
    fn slice(&self) -> &DeviceSlice<T>;

    fn stride(&self) -> usize {
        self.slice().len()
    }

    fn offset(&self) -> usize {
        0
    }

    fn rows(&self) -> usize {
        self.stride()
    }

    fn cols(&self) -> usize {
        self.slice().len() / self.stride()
    }

    fn as_ptr(&self) -> *const T {
        ptr_from_slice_and_offset(self.slice(), self.offset())
    }

    fn as_ptr_and_stride(&self) -> PtrAndStride<T> {
        PtrAndStride::new(self.as_ptr(), self.stride())
    }
}

pub trait DeviceMatrixChunkMutImpl<T>: DeviceMatrixChunkImpl<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T>;

    fn as_mut_ptr(&mut self) -> *mut T {
        let offset = self.offset();
        mut_ptr_from_slice_and_offset(self.slice_mut(), offset)
    }

    fn as_mut_ptr_and_stride(&mut self) -> MutPtrAndStride<T> {
        MutPtrAndStride::new(self.as_mut_ptr(), self.stride())
    }
}

impl<T> DeviceVectorImpl<T> for DeviceVariable<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorMutImpl<T> for DeviceVariable<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorChunkImpl<T> for DeviceVariable<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorChunkMutImpl<T> for DeviceVariable<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixImpl<T> for DeviceVariable<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixMutImpl<T> for DeviceVariable<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceVariable<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DeviceVariable<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorImpl<T> for DeviceSlice<T> {
    fn slice(&self) -> &Self {
        self
    }
}

impl<T> DeviceVectorMutImpl<T> for DeviceSlice<T> {
    fn slice_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T> DeviceVectorChunkImpl<T> for DeviceSlice<T> {
    fn slice(&self) -> &Self {
        self
    }
}

impl<T> DeviceVectorChunkMutImpl<T> for DeviceSlice<T> {
    fn slice_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T> DeviceMatrixImpl<T> for DeviceSlice<T> {
    fn slice(&self) -> &Self {
        self
    }
}

impl<T> DeviceMatrixMutImpl<T> for DeviceSlice<T> {
    fn slice_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceSlice<T> {
    fn slice(&self) -> &Self {
        self
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DeviceSlice<T> {
    fn slice_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T> DeviceVectorImpl<T> for DeviceAllocation<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorMutImpl<T> for DeviceAllocation<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorChunkImpl<T> for DeviceAllocation<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorChunkMutImpl<T> for DeviceAllocation<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixImpl<T> for DeviceAllocation<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixMutImpl<T> for DeviceAllocation<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceAllocation<T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DeviceAllocation<T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorMutImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorChunkImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceVectorChunkMutImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixMutImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DevicePoolAllocation<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self
    }
}

#[derive(Debug)]
pub struct DeviceVectorChunk<'a, T> {
    slice: &'a DeviceSlice<T>,
    offset: usize,
    len: usize,
}

impl<'a, T> DeviceVectorChunk<'a, T> {
    pub fn new(slice: &'a DeviceSlice<T>, offset: usize, len: usize) -> Self {
        assert!(offset + len <= slice.len());
        Self { slice, offset, len }
    }
}

impl<T> DeviceVectorChunkImpl<T> for DeviceVectorChunk<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn rows(&self) -> usize {
        self.len
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceVectorChunk<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn rows(&self) -> usize {
        self.len
    }
}

#[derive(Debug)]
pub struct DeviceVectorChunkMut<'a, T> {
    slice: &'a mut DeviceSlice<T>,
    offset: usize,
    len: usize,
}

impl<'a, T> DeviceVectorChunkMut<'a, T> {
    pub fn new(slice: &'a mut DeviceSlice<T>, offset: usize, len: usize) -> Self {
        assert!(offset + len <= slice.len());
        Self { slice, offset, len }
    }
}

impl<T> DeviceVectorChunkImpl<T> for DeviceVectorChunkMut<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn rows(&self) -> usize {
        self.len
    }
}

impl<T> DeviceVectorChunkMutImpl<T> for DeviceVectorChunkMut<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self.slice
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceVectorChunkMut<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn rows(&self) -> usize {
        self.len
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DeviceVectorChunkMut<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self.slice
    }
}

#[derive(Debug)]
pub struct DeviceMatrix<'a, T> {
    slice: &'a DeviceSlice<T>,
    stride: usize,
}

impl<'a, T> DeviceMatrix<'a, T> {
    pub fn new(slice: &'a DeviceSlice<T>, stride: usize) -> Self {
        assert_eq!(slice.len() % stride, 0);
        Self { slice, stride }
    }
}

impl<T> DeviceMatrixImpl<T> for DeviceMatrix<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn stride(&self) -> usize {
        self.stride
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceMatrix<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn stride(&self) -> usize {
        self.stride
    }
}

#[derive(Debug)]
pub struct DeviceMatrixMut<'a, T> {
    slice: &'a mut DeviceSlice<T>,
    stride: usize,
}

impl<'a, T> DeviceMatrixMut<'a, T> {
    pub fn new(slice: &'a mut DeviceSlice<T>, stride: usize) -> Self {
        assert_eq!(slice.len() % stride, 0);
        Self { slice, stride }
    }
}

impl<T> DeviceMatrixImpl<T> for DeviceMatrixMut<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn stride(&self) -> usize {
        self.stride
    }
}

impl<T> DeviceMatrixMutImpl<T> for DeviceMatrixMut<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self.slice
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceMatrixMut<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn stride(&self) -> usize {
        self.stride
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DeviceMatrixMut<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self.slice
    }
}

#[derive(Debug)]
pub struct DeviceMatrixChunk<'a, T> {
    slice: &'a DeviceSlice<T>,
    stride: usize,
    offset: usize,
    rows: usize,
}

impl<'a, T> DeviceMatrixChunk<'a, T> {
    pub fn new(slice: &'a DeviceSlice<T>, stride: usize, offset: usize, rows: usize) -> Self {
        assert_eq!(slice.len() % stride, 0);
        assert!(offset + rows <= stride);
        Self {
            slice,
            stride,
            offset,
            rows,
        }
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceMatrixChunk<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn stride(&self) -> usize {
        self.stride
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn rows(&self) -> usize {
        self.rows
    }
}

#[derive(Debug)]
pub struct DeviceMatrixChunkMut<'a, T> {
    slice: &'a mut DeviceSlice<T>,
    stride: usize,
    offset: usize,
    rows: usize,
}

impl<'a, T> DeviceMatrixChunkMut<'a, T> {
    pub fn new(slice: &'a mut DeviceSlice<T>, stride: usize, offset: usize, rows: usize) -> Self {
        assert_eq!(slice.len() % stride, 0);
        assert!(offset + rows <= stride);
        Self {
            slice,
            stride,
            offset,
            rows,
        }
    }
}

impl<T> DeviceMatrixChunkImpl<T> for DeviceMatrixChunkMut<'_, T> {
    fn slice(&self) -> &DeviceSlice<T> {
        self.slice
    }

    fn stride(&self) -> usize {
        self.stride
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn rows(&self) -> usize {
        self.rows
    }
}

impl<T> DeviceMatrixChunkMutImpl<T> for DeviceMatrixChunkMut<'_, T> {
    fn slice_mut(&mut self) -> &mut DeviceSlice<T> {
        self.slice
    }
}
