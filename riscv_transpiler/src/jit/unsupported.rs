use super::*;
use std::ptr::NonNull;

const UNSUPPORTED_JIT_MESSAGE: &str =
    "riscv_transpiler JIT is only implemented on x86_64 targets; this build exposes stubs so downstream crates can compile, but any JIT execution will panic at runtime";

#[cold]
#[track_caller]
fn unsupported_jit() -> ! {
    panic!("{UNSUPPORTED_JIT_MESSAGE}");
}

/// Keeps the public JIT context shape available on unsupported targets so
/// downstream crates can still compile against the same API surface.
#[repr(C)]
pub struct Context<I: ContextImpl> {
    pub implementation: I,
}

impl<I: ContextImpl> Context<I> {
    pub fn take_final_state(&mut self) -> Option<MachineState> {
        self.implementation.take_final_state()
    }

    pub fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        self.implementation.final_state_ref()
    }
}

/// Placeholder JIT handle for non-x86_64 targets. Construction succeeds so
/// callers can cache the handle, but any execution path panics explicitly.
pub struct JittedCode<I: ContextImpl> {
    _marker: core::marker::PhantomData<I>,
}

unsafe impl<I: ContextImpl> Send for JittedCode<I> {}

unsafe impl<I: ContextImpl> Sync for JittedCode<I> {}

impl<I: ContextImpl> JittedCode<I> {
    pub fn preprocess_bytecode(_program: &[u32], _cycles_bound: Option<u32>) -> Self {
        Self {
            _marker: core::marker::PhantomData,
        }
    }

    pub fn run(
        &self,
        _context: &mut Context<I>,
        _memory: &mut MemoryHolder,
        _initial_trace_chunk: NonNull<TraceChunk>,
        _initial_memory: &[u32],
    ) {
        unsupported_jit()
    }

    pub fn run_over_prepared_memory(
        &self,
        _context: &mut Context<I>,
        _memory: &mut MemoryHolder,
        _initial_trace_chunk: NonNull<TraceChunk>,
    ) {
        unsupported_jit()
    }
}

impl<N: NonDeterminismCSRSource> JittedCode<DefaultContextImpl<'_, N>> {
    pub fn run_alternative_simulator(
        _program: &[u32],
        _non_determinism_source: &mut N,
        _initial_memory: &[u32],
        _cycles_bound: Option<u32>,
    ) -> (MachineState, Box<MemoryHolder>) {
        unsupported_jit()
    }

    pub fn run_alternative_simulator_with_last_snapshot(
        _program: &[u32],
        _non_determinism_source: &mut N,
        _initial_memory: &[u32],
        _cycles_bound: Option<u32>,
    ) -> (MachineState, Box<MemoryHolder>, Box<TraceChunk>) {
        unsupported_jit()
    }
}
