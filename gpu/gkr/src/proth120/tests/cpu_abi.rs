use std::sync::Arc;

use crate::proth120::forward::challenge_banks::ForwardChallengeDesc;
use crate::proth120::forward::desc::FwdVmDesc;
use crate::proth120::forward::setup::ForwardSetupLookupBatchPr;
use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofLayoutPr;
use crate::upstream::{GKRCircuitArtifact, PR};
use gpu_trace::witness::circuit_type::CircuitType;

pub(crate) fn programs() -> GkrProgramsPr {
    let artifact: GKRCircuitArtifact<PR> = serde_json::from_slice(include_bytes!(
        "../../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .unwrap();
    GkrProgramsPr::compile(CircuitType::L1Wrap, Arc::new(artifact))
}

#[test]
fn cpu_pr_complete_launch_argument_abi() {
    let programs = programs();
    let config = prover::gkr::prover_config::ProofProfile::L1Wrap.prover_config(
        21,
        prover::definitions::SoundnessMode::PessimisticConjecture,
    );
    let layout = ProofLayoutPr::new(&programs, &config);
    let circuit = &programs.runtime_circuit;
    let _gather = crate::proth120::base_layer_claims::BaseClaimGatherPr::new(
        &programs,
        &layout,
        circuit.memory_layout.total_width,
        circuit.witness_layout.total_width,
        circuit.generic_lookup_tables_width,
    );
    layout.validate_geometry(
        &programs.runtime_circuit,
        config.sumcheck_explicit_output_size_log_2,
    );
    let output_columns = programs
        .runtime_circuit
        .global_output_map
        .values()
        .map(Vec::len)
        .sum::<usize>();
    assert_eq!(
        layout.output_evaluations_range.len(),
        (output_columns << config.sumcheck_explicit_output_size_log_2) * 16
    );
    let layer_zero = layout.backward_layers.last().unwrap();
    assert_eq!(layer_zero.final_step_eval_addresses.len(), 111);
    assert_eq!(layer_zero.extra_evaluations_addresses.len(), 15);
    let layer_one = layout
        .backward_layers
        .iter()
        .find(|layer| layer.layer_idx == 1)
        .unwrap();
    assert_eq!(layer_one.extra_evaluations_addresses.len(), 40);
    assert_eq!(
        crate::proth120::backward::main_layer::scratch_last_reader_layer(&programs, &layout),
        Some(1)
    );
    assert!(layout
        .backward_layers
        .iter()
        .filter(|layer| layer.layer_idx > 1)
        .all(|layer| layer.extra_evaluations_addresses.is_empty()));
    assert_eq!(layout.memory_claims.end, layout.setup_claims.start);
    let mut rows = vec![
        ("ab_pr_gkr_fwd_vm_kernel", size_of::<FwdVmDesc>()),
        (
            "ab_pr_gkr_forward_challenge_banks_kernel",
            (32 + size_of::<ForwardChallengeDesc>()).next_multiple_of(8),
        ),
        (
            "ab_pr_gkr_dim_reducing_forward_tower_kernel",
            size_of::<crate::forward::kernels::GpuGKRDimensionReducingForwardTowerBatch<PR>>(),
        ),
        (
            "ab_pr_gkr_forward_setup_generic_lookup_batch_kernel",
            (size_of::<ForwardSetupLookupBatchPr>() + 4).next_multiple_of(8),
        ),
        ("ab_pr_gkr_initial_inner_product_kernel", 32),
        ("ab_pr_gkr_build_eq_group_tables_kernel", 24),
        ("ab_pr_gkr_build_eq_high_low_from_point_kernel", 40),
        ("ab_pr_gkr_build_eq_values_from_group_tables_kernel", 32),
        (
            "ab_pr_gkr_layer0_extras_kernel",
            crate::proth120::backward::extras::PR_EXTRAS_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_bwd_dr_window_r0_kernel",
            crate::proth120::backward::window_dr::PR_DR_WINDOW_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_bwd_dr_window_continuation_kernel",
            crate::proth120::backward::window_dr::PR_DR_WINDOW_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_dr_tail_megakernel",
            crate::proth120::backward::dr_tail::PR_DR_TAIL_ARGUMENT_BYTES,
        ),
        ("ab_pr_gkr_ops_new_claims_two_var_kernel", 32),
        ("ab_pr_gkr_ops_new_claims_linear_kernel", 32),
        ("ab_pr_gkr_ops_dim_reducing_lsb_lines_kernel", 32),
        (
            "ab_pr_gkr_ops_build_combined_claim_kernel",
            16 + size_of::<crate::gkr_ops::GpuCombinedClaimDesc>() + 16,
        ),
    ];
    let continuation_bytes = size_of::<
        crate::proth120::backward::main_continuation::binding::MainContinuationWindowLaunchBindingPr,
    >();
    assert!(continuation_bytes + 2_048 <= 32_764);
    for &mask in
        crate::proth120::backward::main_continuation_window_manifest::PR_MAIN_CONTINUATION_MASKS
    {
        let symbol: &'static str =
            Box::leak(format!("ab_pr_gkr_bwd_main_cont_{mask:02x}_kernel").into_boxed_str());
        rows.push((symbol, continuation_bytes));
    }
    rows.push((
        "ab_pr_gkr_main_tail_kernel",
        crate::proth120::backward::main_tail::PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES,
    ));
    rows.extend([
        (
            "ab_pr_gkr_bwd_r0_kernel",
            crate::proth120::backward::window::PR_R0_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_bwd_r0_unit_kernel",
            crate::proth120::backward::window::PR_R0_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_bwd_r0_tails_kernel",
            crate::proth120::backward::window::PR_R0_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_bwd_build_fold_weights_kernel",
            crate::proth120::backward::window::PR_FOLD_WEIGHTS_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_window_tail_reduce_kernel",
            crate::proth120::backward::window::PR_WINDOW_TAIL_REDUCE_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_window_tail_kernel",
            crate::proth120::backward::window::PR_WINDOW_TAIL_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_bwd_eval_coefficients_kernel",
            crate::proth120::backward::banks::PR_EVAL_COEFFICIENTS_ARGUMENT_BYTES,
        ),
    ]);
    rows.extend([
        (
            "ab_pr_gkr_gather_base_claims_kernel",
            crate::proth120::base_layer_claims::PR_GATHER_ARGUMENT_BYTES,
        ),
        (
            "ab_pr_gkr_merge_claims_kernel",
            crate::proth120::packed_merge::PR_MERGE_ARGUMENT_BYTES,
        ),
    ]);
    for (symbol, bytes) in rows {
        assert!(
            bytes > 0 && bytes <= 32_764,
            "{symbol}: {bytes} argument bytes"
        );
    }
}
