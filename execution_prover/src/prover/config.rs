use crate::backend::ExecutionBackend;
use execution_prover_model::circuit_type::UnrolledCircuitType;
use execution_prover_model::MachineType;
use riscv_transpiler::vm::SimpleTape;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use type_map::concurrent::TypeMap;

/// - `Unrolled`: per-family circuits (split memory / non-memory / I&T).
/// - `Unified`: the reduced-machine unified circuit (one family,
///   `MachineType::Reduced` only).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExecutionKind {
    Unrolled,
    Unified,
}

pub(super) struct BinaryHolder<B: ExecutionBackend> {
    pub(super) execution_kind: ExecutionKind,
    pub(super) machine_type: MachineType,
    pub(super) binary_image: Arc<Box<[u32]>>,
    pub(super) text_section: Arc<Box<[u32]>>,
    pub(super) cycles_bound: Option<u32>,
    pub(super) jit_cache: Arc<Mutex<TypeMap>>,
    pub(super) instruction_tape: Arc<SimpleTape>,
    pub(super) precomputations: HashMap<UnrolledCircuitType, B::Precomputations>,
}
