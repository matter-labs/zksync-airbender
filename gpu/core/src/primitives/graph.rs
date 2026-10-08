//! CUDA graph capture of stream work.
//!
//! Capture uses thread-local mode, so CUDA calls on other threads (pinned host
//! allocations by other workers, for example) do not invalidate it.

use std::cell::Cell;
use std::ffi::c_void;
use std::ptr::null_mut;

use era_cudart::execution::{Dim3, KernelArguments, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaError_t, cudaStream_t, cuda_fn_and_stub, dim3};

type GraphHandle = *mut c_void;
type GraphExecHandle = *mut c_void;
type NodeHandle = *mut c_void;

const STREAM_CAPTURE_MODE_THREAD_LOCAL: u32 = 1;
const STREAM_CAPTURE_STATUS_ACTIVE: u32 = 1;

#[repr(C)]
#[derive(Clone, Copy)]
struct KernelNodeParams {
    func: *const c_void,
    grid_dim: dim3,
    block_dim: dim3,
    shared_mem_bytes: u32,
    kernel_params: *mut *mut c_void,
    extra: *mut *mut c_void,
}

cuda_fn_and_stub! {
    fn cudaStreamBeginCapture(stream: cudaStream_t, mode: u32) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaStreamEndCapture(stream: cudaStream_t, graph: *mut GraphHandle) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaGraphInstantiateWithFlags(
        exec: *mut GraphExecHandle,
        graph: GraphHandle,
        flags: u64,
    ) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaGraphLaunch(exec: GraphExecHandle, stream: cudaStream_t) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaStreamGetCaptureInfo(
        stream: cudaStream_t,
        status: *mut u32,
        id: *mut u64,
        graph: *mut GraphHandle,
        dependencies: *mut *const NodeHandle,
        edge_data: *mut *const c_void,
        dependency_count: *mut usize,
    ) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaGraphExecKernelNodeSetParams(
        exec: GraphExecHandle,
        node: NodeHandle,
        params: *const KernelNodeParams,
    ) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaGraphKernelNodeGetParams(node: NodeHandle, params: *mut KernelNodeParams) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaFuncGetParamCount(func: *const c_void, count: *mut usize) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaFuncGetParamInfo(
        func: *const c_void,
        index: usize,
        offset: *mut usize,
        size: *mut usize,
    ) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaGraphExecDestroy(exec: GraphExecHandle) -> cudaError_t;
}
cuda_fn_and_stub! {
    fn cudaGraphDestroy(graph: GraphHandle) -> cudaError_t;
}

thread_local! {
    static CAPTURING: Cell<bool> = const { Cell::new(false) };
}

/// Whether this thread is inside [`CudaGraph::capture`].
pub fn is_capturing() -> bool {
    CAPTURING.get()
}

/// A node of a captured graph, valid for the graph and the execs made from it.
#[derive(Copy, Clone)]
pub struct GraphNode(NodeHandle);

/// The node of the operation most recently captured on `stream`.
pub fn last_captured_node(stream: &CudaStream) -> CudaResult<GraphNode> {
    let mut status = 0;
    let mut dependencies = null_mut::<NodeHandle>().cast_const();
    let mut count = 0;
    unsafe {
        cudaStreamGetCaptureInfo(
            stream.into(),
            &mut status,
            null_mut(),
            null_mut(),
            &mut dependencies,
            null_mut(),
            &mut count,
        )
    }
    .wrap()?;
    assert_eq!(
        status, STREAM_CAPTURE_STATUS_ACTIVE,
        "stream is not capturing"
    );
    assert_eq!(count, 1, "expected one captured node to follow");
    Ok(GraphNode(unsafe { *dependencies }))
}

impl GraphNode {
    /// Launch geometry and argument bytes of this kernel node as captured.
    pub fn captured_kernel_launch(self) -> CudaResult<CapturedKernelLaunch> {
        let mut params = KernelNodeParams {
            func: std::ptr::null(),
            grid_dim: dim3 { x: 0, y: 0, z: 0 },
            block_dim: dim3 { x: 0, y: 0, z: 0 },
            shared_mem_bytes: 0,
            kernel_params: null_mut(),
            extra: null_mut(),
        };
        unsafe { cudaGraphKernelNodeGetParams(self.0, &mut params) }.wrap()?;
        let mut count = 0;
        unsafe { cudaFuncGetParamCount(params.func, &mut count) }.wrap()?;
        let mut args = Vec::with_capacity(count);
        for index in 0..count {
            let (mut offset, mut size) = (0, 0);
            unsafe { cudaFuncGetParamInfo(params.func, index, &mut offset, &mut size) }.wrap()?;
            let mut words = vec![0u64; size.div_ceil(8)].into_boxed_slice();
            // SAFETY: the graph stores `size` bytes for argument `index`.
            unsafe {
                std::ptr::copy_nonoverlapping(
                    *params.kernel_params.add(index) as *const u8,
                    words.as_mut_ptr().cast::<u8>(),
                    size,
                )
            };
            args.push((words, size));
        }
        params.kernel_params = null_mut();
        Ok(CapturedKernelLaunch { params, args })
    }
}

/// A captured kernel launch with owned argument bytes, re-applied to an
/// instantiated graph after patching some of them.
#[derive(Clone)]
pub struct CapturedKernelLaunch {
    params: KernelNodeParams,
    args: Vec<(Box<[u64]>, usize)>,
}

impl CapturedKernelLaunch {
    /// Overwrites the leading `u32` of argument `arg`.
    pub fn patch_leading_u32(&mut self, arg: usize, value: u32) {
        let (words, size) = &mut self.args[arg];
        assert!(*size >= 4, "kernel argument {arg} is smaller than a u32");
        // SAFETY: the argument holds at least 4 bytes.
        unsafe {
            std::ptr::copy_nonoverlapping(
                value.to_ne_bytes().as_ptr(),
                words.as_mut_ptr().cast::<u8>(),
                4,
            )
        };
    }
}

pub struct CudaGraph(GraphHandle);

impl CudaGraph {
    /// Captures every operation `f` enqueues on `stream` instead of executing
    /// it. Host code in `f` runs normally.
    pub fn capture<R>(
        stream: &CudaStream,
        f: impl FnOnce() -> CudaResult<R>,
    ) -> CudaResult<(Self, R)> {
        assert!(!is_capturing(), "nested CUDA graph capture");
        unsafe { cudaStreamBeginCapture(stream.into(), STREAM_CAPTURE_MODE_THREAD_LOCAL) }
            .wrap()?;
        CAPTURING.set(true);
        let result = f();
        CAPTURING.set(false);
        let mut graph = null_mut();
        let ended = unsafe { cudaStreamEndCapture(stream.into(), &mut graph) }.wrap();
        let graph = Self(graph);
        let value = result?;
        ended?;
        Ok((graph, value))
    }

    pub fn instantiate(&self) -> CudaResult<CudaGraphExec> {
        let mut exec = null_mut();
        unsafe { cudaGraphInstantiateWithFlags(&mut exec, self.0, 0) }.wrap()?;
        Ok(CudaGraphExec(exec))
    }
}

impl Drop for CudaGraph {
    fn drop(&mut self) {
        if !self.0.is_null() {
            unsafe { cudaGraphDestroy(self.0) }
                .wrap()
                .expect("cudaGraphDestroy failed");
        }
    }
}

/// An instantiated graph. Dropping it while a launch is in flight is allowed;
/// CUDA frees it once the launch completes.
pub struct CudaGraphExec(GraphExecHandle);

impl CudaGraphExec {
    pub fn launch(&self, stream: &CudaStream) -> CudaResult<()> {
        unsafe { cudaGraphLaunch(self.0, stream.into()) }.wrap()
    }

    /// Applies `launch` to kernel node `node`.
    pub fn set_captured_kernel_node(
        &self,
        node: GraphNode,
        launch: &CapturedKernelLaunch,
    ) -> CudaResult<()> {
        let mut pointers: Vec<*mut c_void> = launch
            .args
            .iter()
            .map(|(words, _)| words.as_ptr() as *mut c_void)
            .collect();
        let params = KernelNodeParams {
            kernel_params: pointers.as_mut_ptr(),
            ..launch.params
        };
        unsafe { cudaGraphExecKernelNodeSetParams(self.0, node.0, &params) }.wrap()
    }

    /// Replaces the launch geometry and arguments of kernel node `node`, which
    /// launches without dynamic shared memory.
    pub fn set_kernel_node<F: KernelFunction>(
        &self,
        node: GraphNode,
        function: &F,
        grid_dim: Dim3,
        block_dim: Dim3,
        args: &impl KernelArguments<Signature = F::Signature>,
    ) -> CudaResult<()> {
        let mut raw_args = args.as_raw();
        let params = KernelNodeParams {
            func: function.as_ptr(),
            grid_dim: grid_dim.into(),
            block_dim: block_dim.into(),
            shared_mem_bytes: 0,
            kernel_params: raw_args.as_mut_ptr(),
            extra: null_mut(),
        };
        unsafe { cudaGraphExecKernelNodeSetParams(self.0, node.0, &params) }.wrap()
    }
}

impl Drop for CudaGraphExec {
    fn drop(&mut self) {
        unsafe { cudaGraphExecDestroy(self.0) }
            .wrap()
            .expect("cudaGraphExecDestroy failed");
    }
}
