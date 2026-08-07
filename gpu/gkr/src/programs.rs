//! Per-circuit symbolic programs used by the GPU GKR interpreters.
//!
//! Forward search is deliberately absent from this module. The searched
//! schedules are committed artifacts embedded in the binary; initialization
//! only lowers the circuit, rejects an artifact mismatch, and compiles the
//! forward, R0, and continuation programs once.

use gpu_core::primitives::field::BF;
use gpu_gkr_compiler::{
    compile_continuations, compile_forward, compile_r0, parse_forward_artifact,
    ContinuationProgramBundle, ForwardProgramBundle, R0ProgramBundle, WindowFamily,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use std::sync::Arc;

use crate::transform::normalize_compiled_circuit_for_gpu;
use crate::upstream::{GKRAddress, GKRCircuitArtifact, VirtualSetupPoly};

#[derive(Clone)]
pub(crate) struct BackwardLayerPlan {
    pub(crate) inputs: Vec<GKRAddress>,
    pub(crate) claims: Vec<(usize, GKRAddress)>,
}

fn sink_address(sink: &gkr_eval_ir::SinkKind) -> Option<GKRAddress> {
    match *sink {
        gkr_eval_ir::SinkKind::Inner { layer, offset } => {
            Some(GKRAddress::InnerLayer { layer, offset })
        }
        gkr_eval_ir::SinkKind::Cache { layer, offset } => {
            Some(GKRAddress::Cached { layer, offset })
        }
        gkr_eval_ir::SinkKind::Scratch { slot } => Some(GKRAddress::ScratchSpace(slot)),
    }
}

fn bound_window_address(family: WindowFamily, column: usize) -> GKRAddress {
    match family {
        WindowFamily::BaseLayerMemory => GKRAddress::BaseLayerMemory(column),
        WindowFamily::BaseLayerWitness => GKRAddress::BaseLayerWitness(column),
        WindowFamily::Setup => GKRAddress::Setup(column),
        WindowFamily::Scratch => GKRAddress::ScratchSpace(column),
        WindowFamily::LayerOutput { layer, .. } => GKRAddress::InnerLayer {
            layer,
            offset: column,
        },
        WindowFamily::CacheOutput { layer, .. } => GKRAddress::Cached {
            layer,
            offset: column,
        },
        WindowFamily::VirtualSetup { kind } => GKRAddress::VirtualSetup(match kind {
            0 => VirtualSetupPoly::RangeCheck16Bits,
            1 => VirtualSetupPoly::RangeCheckTimestamp,
            2 => VirtualSetupPoly::InitsAndTeardownsLow,
            3 => VirtualSetupPoly::InitsAndTeardownsHigh,
            _ => panic!("unknown virtual setup kind {kind}"),
        }),
    }
}

pub(crate) fn backward_layer_plans(
    dag: &gkr_eval_ir::DagCircuit,
    continuations: &ContinuationProgramBundle,
) -> Vec<BackwardLayerPlan> {
    dag.layers
        .iter()
        .zip(&continuations.layers)
        .map(|(layer, continuation)| {
            let inputs = continuation
                .binding
                .windows
                .iter()
                .flat_map(|window| {
                    window
                        .columns
                        .iter()
                        .map(|column| bound_window_address(window.family, column.column))
                })
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            let claims = layer
                .batching
                .roots
                .iter()
                .enumerate()
                .filter_map(|(offset, root)| {
                    let root = &layer.roots[root.0 as usize];
                    root.claim.as_ref()?;
                    root.materialize.as_ref().map(|sink| {
                        (
                            offset,
                            sink_address(&sink.kind)
                                .expect("main-layer output must have an addressable sink"),
                        )
                    })
                })
                .collect();
            BackwardLayerPlan { inputs, claims }
        })
        .collect()
}

const ADD_SUB: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/add_sub_lui_auipc_mop_schedule_b4_gkr.json");
const BIGINT: &[u8] = include_bytes!(
    "../../../cs/compiled_circuits/bigint_with_extended_control_schedule_b4_gkr.json"
);
const BLAKE2_G: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/blake2_g_function_schedule_b4_gkr.json");
const BLAKE2_EXT: &[u8] = include_bytes!(
    "../../../cs/compiled_circuits/blake2_with_extended_control_schedule_b4_gkr.json"
);
const INITS: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/inits_and_teardowns_schedule_b4_gkr.json");
const JUMP: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/jump_branch_slt_schedule_b4_gkr.json");
const KECCAK: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/keccak_special5_schedule_b4_gkr.json");
const MEM_SUBWORD: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/mem_subword_only_schedule_b4_gkr.json");
const MEM_WORD: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/mem_word_only_schedule_b4_gkr.json");
const SHIFT: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/shift_binop_schedule_b4_gkr.json");
const UNIFIED: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/unified_reduced_machine_schedule_b4_gkr.json");
const UNSIGNED_MUL_DIV: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/unsigned_mul_div_schedule_b4_gkr.json");

fn forward_artifact(circuit_type: CircuitType) -> (&'static [u8], &'static str) {
    match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => (ADD_SUB, "add_sub_lui_auipc_mop"),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => (JUMP, "jump_branch_slt"),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => (UNSIGNED_MUL_DIV, "unsigned_mul_div"),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )) => (SHIFT, "shift_binop"),
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => (MEM_WORD, "mem_word_only"),
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => (MEM_SUBWORD, "mem_subword_only"),
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            (INITS, "inits_and_teardowns")
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => (UNIFIED, "unified_reduced_machine"),
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            (BIGINT, "bigint_with_extended_control")
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            (BLAKE2_EXT, "blake2_with_extended_control")
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
            (BLAKE2_G, "blake2_g_function")
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            (KECCAK, "keccak_special5")
        }
    }
}

/// Symbolic programs compiled once with the circuit's other precomputations.
///
/// R0 and continuation remain separate compiler products and separate runtime
/// inputs; they intentionally share no policy object.
pub struct GkrPrograms {
    circuit_type: CircuitType,
    compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    runtime_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub(crate) forward: ForwardProgramBundle,
    pub(crate) r0: R0ProgramBundle,
    pub(crate) continuations: ContinuationProgramBundle,
    pub(crate) backward_layers: Vec<BackwardLayerPlan>,
}

impl GkrPrograms {
    pub fn compile(
        circuit_type: CircuitType,
        artifact: Arc<GKRCircuitArtifact<BF>>,
    ) -> Result<Self, String> {
        let runtime_circuit = Arc::new(normalize_compiled_circuit_for_gpu(
            artifact.as_ref().clone(),
        ));
        let dag = gkr_eval_ir::lower_dag(&artifact)?;
        let (bytes, expected_circuit) = forward_artifact(circuit_type);
        let searched = parse_forward_artifact(bytes, "embedded forward GKR schedule")
            .map_err(|error| error.to_string())?;
        if searched.circuit != expected_circuit {
            return Err(format!(
                "embedded forward GKR schedule is for {}, expected {expected_circuit}",
                searched.circuit
            ));
        }
        if searched.budget_buckets != 4 {
            return Err(format!(
                "embedded forward GKR schedule has E4 budget {}, expected 4",
                searched.budget_buckets
            ));
        }
        let forward = compile_forward(&dag, &searched)
            .map_err(|error| format!("forward GKR compile: {error:?}"))?;

        let r0 = compile_r0(&dag).map_err(|error| format!("R0 GKR compile: {error:?}"))?;
        let continuations = compile_continuations(&dag)
            .map_err(|error| format!("continuation GKR compile: {error:?}"))?;
        let backward_layers = backward_layer_plans(&dag, &continuations);

        Ok(Self {
            circuit_type,
            compiled_circuit: artifact,
            runtime_circuit,
            forward,
            r0,
            continuations,
            backward_layers,
        })
    }

    pub fn circuit_type(&self) -> CircuitType {
        self.circuit_type
    }

    pub fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.compiled_circuit
    }

    pub(crate) fn runtime_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.runtime_circuit
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

#[cfg(test)]
mod tests {
    use super::*;
    use gpu_gkr_compiler::{LeanBoundColumn, LeanBoundWindow, LeanSourceBinding};
    use std::collections::BTreeSet;

    #[test]
    fn bound_inputs_include_cache_and_virtual_setup_sources() {
        let binding = LeanSourceBinding {
            windows: vec![
                LeanBoundWindow {
                    family: WindowFamily::CacheOutput {
                        layer: 2,
                        ext: true,
                    },
                    first_column: 7,
                    columns: vec![LeanBoundColumn {
                        column: 7,
                        source: 0,
                    }],
                },
                LeanBoundWindow {
                    family: WindowFamily::VirtualSetup { kind: 0 },
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 1,
                    }],
                },
            ],
            source_count: 0,
        };
        let inputs: BTreeSet<_> = binding
            .windows
            .iter()
            .flat_map(|window| {
                window
                    .columns
                    .iter()
                    .map(|column| bound_window_address(window.family, column.column))
            })
            .collect();
        assert_eq!(
            inputs,
            BTreeSet::from([
                GKRAddress::Cached {
                    layer: 2,
                    offset: 7
                },
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
            ])
        );
    }
}
