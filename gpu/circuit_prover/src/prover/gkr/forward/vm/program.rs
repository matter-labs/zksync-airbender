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

use std::sync::OnceLock;

use gkr_eval_isa::fwd::compile::{compile_circuit, parse_committed_schedule, CompiledCircuit};

use crate::primitives::field::BF;
use crate::upstream::{lower_dag, validate_dag, GKRCircuitArtifact};

/// The committed b16 schedule for `add_sub_lui_auipc_mop`, embedded so no
/// source-tree path is read at runtime. add_sub is the only circuit in scope
/// for the forward VM; the caller's structural predicate
/// (`generated_layer0::is_add_sub_cached_layout`) is what keeps another
/// circuit from reaching here.
pub(crate) const EMBEDDED_ADD_SUB_SCHEDULE: &[u8] = include_bytes!(
    "../../../../../../../cs/compiled_circuits/add_sub_lui_auipc_mop_schedule_b16_gkr.json"
);

/// Compile the embedded program for `artifact`, once per process.
///
/// Cached in a `OnceLock` like
/// [`super::super::generated_layer0::generated_layer0_enabled`]: one circuit,
/// one program. The error is stringified so the cache can hand out the same
/// failure to every later caller instead of retrying a compile that cannot
/// start succeeding.
pub(crate) fn compiled_program(
    artifact: &GKRCircuitArtifact<BF>,
) -> Result<&'static CompiledCircuit, String> {
    static PROGRAM: OnceLock<Result<CompiledCircuit, String>> = OnceLock::new();
    PROGRAM
        .get_or_init(|| compile_program_from_bytes(EMBEDDED_ADD_SUB_SCHEDULE, artifact))
        .as_ref()
        .map_err(Clone::clone)
}

/// The compile chain itself, over an explicit schedule so the negative cases
/// are testable.
pub(crate) fn compile_program_from_bytes(
    schedule_bytes: &[u8],
    artifact: &GKRCircuitArtifact<BF>,
) -> Result<CompiledCircuit, String> {
    let schedule = parse_committed_schedule(schedule_bytes, "embedded forward-VM schedule")
        .map_err(|e| format!("{e:?}"))?;
    let dag = lower_dag(artifact).map_err(|e| format!("lower_dag: {e}"))?;
    validate_dag(&dag).map_err(|e| format!("validate: {e}"))?;
    compile_circuit(&dag, &schedule, artifact).map_err(|e| format!("compile_circuit: {e:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::upstream::GKRCircuitArtifact;

    fn add_sub_artifact() -> GKRCircuitArtifact<BF> {
        crate::prover::tests::deserialize_json_for_test(
            "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
        )
    }

    /// The bench compile chain finds its schedule through
    /// `env!("CARGO_MANIFEST_DIR")` joined to a source-tree path, which does not
    /// exist in a shipped binary. This is the same chain reading bytes that
    /// travel with the executable.
    #[test]
    fn the_embedded_schedule_compiles_add_sub_with_no_source_tree_path() {
        let artifact = add_sub_artifact();
        let program = compile_program_from_bytes(EMBEDDED_ADD_SUB_SCHEDULE, &artifact)
            .expect("the embedded schedule must compile against the add_sub artifact");

        assert_eq!(program.layers.len(), artifact.layers.len());
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
        let program = compile_program_from_bytes(EMBEDDED_ADD_SUB_SCHEDULE, &add_sub_artifact())
            .expect("the embedded schedule must compile");
        assert_eq!(program.budget, super::super::FWD_VM_S4_BUDGET_LANES as usize);
    }

    /// Proves the schedule is validated against the artifact rather than
    /// trusted: another circuit's committed schedule is well-formed JSON and
    /// deserializes fine, so only validation can reject it.
    #[test]
    fn a_schedule_for_a_different_circuit_is_rejected() {
        let other = std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../cs/compiled_circuits/mem_word_only_schedule_b16_gkr.json"),
        )
        .expect("committed mem_word_only schedule must exist");

        let err = compile_program_from_bytes(&other, &add_sub_artifact())
            .expect_err("a schedule for another circuit must not compile against add_sub");
        assert!(
            err.contains("InvalidSchedule"),
            "it must be rejected by schedule validation, not by parsing, got: {err}"
        );
    }

    #[test]
    fn bytes_that_are_not_a_schedule_are_rejected() {
        let err = compile_program_from_bytes(b"{}", &add_sub_artifact())
            .expect_err("an empty JSON object is not a CircuitSchedule");
        assert!(
            err.contains("parse embedded forward-VM schedule"),
            "it must fail at the parse, before the DAG is lowered, got: {err}"
        );
    }
}
