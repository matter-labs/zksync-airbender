//! The forward VM's compiled program, built from bytes embedded in the binary.
//!
//! The A/B bench compiles the same program, but it is not shippable: it reads
//! the committed schedule through `env!("CARGO_MANIFEST_DIR")` joined to a
//! source-tree path (`bench_interp::fwd_vm::compile`), which exists only on the
//! machine that built the binary. Here the schedule travels *inside* the
//! executable, and the artifact comes from the caller — production already has
//! it.
//!
//! The chain is the upstream production one, unchanged:
//! `lower_dag` -> `validate` -> `compile_circuit`. `compile_circuit` runs
//! `validate_circuit_schedule` against the lowered DAG before it touches a
//! layer, so a schedule that does not describe *this* artifact is rejected
//! rather than silently compiled into a wrong program.
//!
//! The artifact must be the RAW one, before
//! `transform::normalize_compiled_circuit_for_gpu`: the committed schedule was
//! searched against the DAG that `lower_dag` produces from the raw artifact,
//! and normalization rewrites scratch-backed addresses in gate relations. The
//! bench chain makes the same split — `load_fwd_vm_circuit` compiles from the
//! raw artifact while `CircuitFixture` normalizes for storage.

use gpu_gkr_compiler::{compile_forward, parse_forward_artifact};
pub(crate) use gpu_gkr_compiler::ForwardProgramBundle as CompiledCircuit;

use crate::witness::circuit_type::CircuitType;
use gkr_eval_ir::DagCircuit;

/// The committed b16 schedule for `add_sub_lui_auipc_mop`, embedded so no
/// source-tree path is read at runtime.
pub(crate) const EMBEDDED_ADD_SUB_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/add_sub_lui_auipc_mop_schedule_b16_gkr.json"
);

/// The committed b16 schedule for `blake2_with_extended_control`, the layout
/// `CircuitType::Delegation(Blake2WithCompression)` proves.
pub(crate) const EMBEDDED_BLAKE2_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/blake2_with_extended_control_schedule_b16_gkr.json"
);

/// The remaining committed b16 schedules — one per corpus layout, all 12 of them.
pub(crate) const EMBEDDED_JUMP_BRANCH_SLT_SCHEDULE: &[u8] =
    include_bytes!("../../../../../../../cs/compiled_circuits/jump_branch_slt_schedule_b16_gkr.json");
pub(crate) const EMBEDDED_UNSIGNED_MUL_DIV_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/unsigned_mul_div_schedule_b16_gkr.json"
);
pub(crate) const EMBEDDED_SHIFT_BINOP_SCHEDULE: &[u8] =
    include_bytes!("../../../../../../../cs/compiled_circuits/shift_binop_schedule_b16_gkr.json");
pub(crate) const EMBEDDED_MEM_WORD_ONLY_SCHEDULE: &[u8] =
    include_bytes!("../../../../../../../cs/compiled_circuits/mem_word_only_schedule_b16_gkr.json");
pub(crate) const EMBEDDED_MEM_SUBWORD_ONLY_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/mem_subword_only_schedule_b16_gkr.json"
);
/// Named `inits_and_teardowns_*`, not `inits_and_teardowns_preprocessed_*` like the
/// layout it schedules — the schedule file predates the layout rename.
pub(crate) const EMBEDDED_INITS_AND_TEARDOWNS_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/inits_and_teardowns_schedule_b16_gkr.json"
);
pub(crate) const EMBEDDED_BIGINT_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/bigint_with_extended_control_schedule_b16_gkr.json"
);
pub(crate) const EMBEDDED_BLAKE2_G_FUNCTION_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/blake2_g_function_schedule_b16_gkr.json"
);
pub(crate) const EMBEDDED_KECCAK_SPECIAL5_SCHEDULE: &[u8] =
    include_bytes!("../../../../../../../cs/compiled_circuits/keccak_special5_schedule_b16_gkr.json");
pub(crate) const EMBEDDED_UNIFIED_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/unified_reduced_machine_schedule_b16_gkr.json"
);

/// The embedded schedule for a circuit. Every corpus circuit has one now, so no
/// arm answers `None` — the `Option` stays because the SHAPE "a circuit may have
/// no schedule" is what the callers are built around, not because any circuit
/// currently lacks one.
///
/// A schedule is SEARCH output — the b16 schedules were searched against each
/// circuit's DAG and are not recomputed at runtime — so unlike the backward
/// coordinates these must travel inside the executable. This table is therefore
/// the forward VM's real allowlist. The match has no wildcard, so a new
/// `CircuitType` variant fails to compile here rather than silently falling back
/// to flat.
pub(crate) fn embedded_forward_artifact(circuit_type: CircuitType) -> &'static [u8] {
    use crate::witness::circuit_type::{
        DelegationCircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };
    use crate::witness::circuit_type::UnrolledMemoryCircuitType;
    match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => EMBEDDED_ADD_SUB_SCHEDULE,
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => EMBEDDED_JUMP_BRANCH_SLT_SCHEDULE,
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => EMBEDDED_UNSIGNED_MUL_DIV_SCHEDULE,
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
        )) => EMBEDDED_SHIFT_BINOP_SCHEDULE,
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => EMBEDDED_MEM_WORD_ONLY_SCHEDULE,
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => EMBEDDED_MEM_SUBWORD_ONLY_SCHEDULE,
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            EMBEDDED_INITS_AND_TEARDOWNS_SCHEDULE
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => EMBEDDED_UNIFIED_SCHEDULE,
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            EMBEDDED_BIGINT_SCHEDULE
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            EMBEDDED_BLAKE2_SCHEDULE
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
            EMBEDDED_BLAKE2_G_FUNCTION_SCHEDULE
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            EMBEDDED_KECCAK_SPECIAL5_SCHEDULE
        }
    }
}

/// Compile the embedded program for `circuit_type`.
///
/// No cache and no lock: this is per-circuit precomputation, built once by the
/// caller (`GkrVmPrograms::compile`) and owned by whatever holds the circuit's
/// other precomputations. `lower_dag` over a multi-megabyte layout has no business
/// running behind a lock on a proving thread.
pub(crate) fn compile_program(
    circuit_type: CircuitType,
    dag: &DagCircuit,
) -> Result<CompiledCircuit, String> {
    compile_program_from_bytes(embedded_forward_artifact(circuit_type), dag)
}

/// The compile chain itself, over an explicit schedule so the negative cases
/// are testable.
pub(crate) fn compile_program_from_bytes(
    schedule_bytes: &[u8],
    dag: &DagCircuit,
) -> Result<CompiledCircuit, String> {
    let schedule = parse_forward_artifact(schedule_bytes, "embedded forward-VM artifact")
        .map_err(|e| format!("{e:?}"))?;
    compile_forward(dag, &schedule).map_err(|e| format!("compile_forward: {e:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::primitives::field::BF;
    use crate::upstream::GKRCircuitArtifact;

    fn add_sub_artifact() -> GKRCircuitArtifact<BF> {
        crate::prover::tests::deserialize_json_for_test(
            "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
        )
    }

    fn add_sub_dag() -> DagCircuit {
        let dag = crate::upstream::lower_dag(&add_sub_artifact()).expect("lower add_sub DAG");
        crate::upstream::validate_dag(&dag).expect("validate add_sub DAG");
        dag
    }

    /// The bench compile chain finds its schedule through
    /// `env!("CARGO_MANIFEST_DIR")` joined to a source-tree path, which does not
    /// exist in a shipped binary. This is the same chain reading bytes that
    /// travel with the executable.
    #[test]
    fn the_embedded_schedule_compiles_add_sub_with_no_source_tree_path() {
        let dag = add_sub_dag();
        let program = compile_program_from_bytes(EMBEDDED_ADD_SUB_SCHEDULE, &dag)
            .expect("the embedded schedule must compile against the add_sub artifact");

        assert_eq!(program.layers.len(), dag.layers.len());
        assert!(
            !program.layers[0].program.instrs.is_empty(),
            "layer 0 is the layer this plan runs on the VM; it must carry a program"
        );
    }

    /// The launcher asserts its own capacity against the budget it is handed
    /// (`vm/mod.rs`), so a program compiled at any other budget cannot be
    /// launched by the s4 kernel. Pin the committed corpus at b16 here rather
    /// than discovering it at the launch site.
    #[test]
    fn the_embedded_program_is_compiled_at_the_s4_budget() {
        let program = compile_program_from_bytes(EMBEDDED_ADD_SUB_SCHEDULE, &add_sub_dag())
            .expect("the embedded schedule must compile");
        assert_eq!(program.budget, super::super::FWD_VM_S4_BUDGET_LANES as usize);
    }

}
