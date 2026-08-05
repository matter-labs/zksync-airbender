//! Per-circuit symbolic programs used by the GPU GKR interpreters.
//!
//! Forward search is deliberately absent from this module. The searched
//! schedules are committed artifacts embedded in the binary; initialization
//! only lowers the circuit, rejects an artifact mismatch, and compiles the
//! forward, R0, and continuation programs once.

use gpu_core::primitives::field::BF;
use gpu_gkr_compiler::{
    compile_continuations, compile_forward, compile_r0, parse_forward_artifact,
    ContinuationProgramBundle, ForwardProgramBundle, GpuResourceProfile, R0ProgramBundle,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

use crate::upstream::GKRCircuitArtifact;

const ADD_SUB: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/add_sub_lui_auipc_mop_schedule_b16_gkr.json");
const BIGINT: &[u8] = include_bytes!(
    "../../../cs/compiled_circuits/bigint_with_extended_control_schedule_b16_gkr.json"
);
const BLAKE2_G: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/blake2_g_function_schedule_b16_gkr.json");
const BLAKE2_EXT: &[u8] = include_bytes!(
    "../../../cs/compiled_circuits/blake2_with_extended_control_schedule_b16_gkr.json"
);
const INITS: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/inits_and_teardowns_schedule_b16_gkr.json");
const JUMP: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/jump_branch_slt_schedule_b16_gkr.json");
const KECCAK: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/keccak_special5_schedule_b16_gkr.json");
const MEM_SUBWORD: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/mem_subword_only_schedule_b16_gkr.json");
const MEM_WORD: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/mem_word_only_schedule_b16_gkr.json");
const SHIFT: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/shift_binop_schedule_b16_gkr.json");
const UNIFIED: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/unified_reduced_machine_schedule_b16_gkr.json");
const UNSIGNED_MUL_DIV: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/unsigned_mul_div_schedule_b16_gkr.json");

fn forward_artifact(circuit_type: CircuitType) -> &'static [u8] {
    match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => ADD_SUB,
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => JUMP,
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => UNSIGNED_MUL_DIV,
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )) => SHIFT,
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => MEM_WORD,
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => MEM_SUBWORD,
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => INITS,
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => UNIFIED,
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => BIGINT,
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => BLAKE2_EXT,
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => BLAKE2_G,
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => KECCAK,
    }
}

/// Symbolic programs compiled once with the circuit's other precomputations.
///
/// R0 and continuation remain separate compiler products and separate runtime
/// inputs; they intentionally share no policy object.
pub struct GkrPrograms {
    pub(crate) forward: ForwardProgramBundle,
    pub(crate) r0: R0ProgramBundle,
    pub(crate) continuations: ContinuationProgramBundle,
}

impl GkrPrograms {
    pub fn compile(
        circuit_type: CircuitType,
        artifact: &GKRCircuitArtifact<BF>,
    ) -> Result<Self, String> {
        let dag = gkr_eval_ir::lower_dag(artifact)?;
        gkr_eval_ir::validate(&dag)?;

        let bytes = forward_artifact(circuit_type);
        let searched = parse_forward_artifact(bytes, "embedded forward GKR schedule")
            .map_err(|error| error.to_string())?;
        let forward = compile_forward(&dag, &searched)
            .map_err(|error| format!("forward GKR compile: {error:?}"))?;

        let resources = GpuResourceProfile::production();
        let r0 =
            compile_r0(&dag, &resources).map_err(|error| format!("R0 GKR compile: {error:?}"))?;
        let continuations = compile_continuations(&dag, &resources)
            .map_err(|error| format!("continuation GKR compile: {error:?}"))?;

        Ok(Self {
            forward,
            r0,
            continuations,
        })
    }

    pub(crate) fn r0_layer(&self, layer: usize) -> &gpu_gkr_compiler::R0LayerProgram {
        &self.r0.layers[layer]
    }

    pub(crate) fn continuation_layer(
        &self,
        layer: usize,
    ) -> &gpu_gkr_compiler::ContinuationLayerProgram {
        &self.continuations.layers[layer]
    }
}
