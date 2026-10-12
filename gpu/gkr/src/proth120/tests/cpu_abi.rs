use std::sync::Arc;

use crate::proth120::forward::challenge_banks::ForwardChallengeDesc;
use crate::proth120::forward::desc::FwdVmDesc;
use crate::proth120::forward::setup::ForwardSetupLookupBatchPr;
use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofLayoutPr;
use crate::upstream::{GKRCircuitArtifact, SecurityLevel, PR};
use gpu_trace::witness::circuit_type::CircuitType;

pub(crate) fn programs() -> GkrProgramsPr {
    let artifact: GKRCircuitArtifact<PR> = serde_json::from_slice(include_bytes!(
        "../../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .unwrap();
    GkrProgramsPr::compile(CircuitType::L1Wrap, Arc::new(artifact)).unwrap()
}

#[test]
fn cpu_pr_complete_launch_argument_abi() {
    let programs = programs();
    let config = prover::gkr::prover_config::example_configs::evm_production_packed_prover_config(
        SecurityLevel::Sec100,
    );
    let layout = ProofLayoutPr::new(&programs, &config);
    layout.validate_geometry(22, 5);
    assert_eq!(layout.output_evaluations_range.len(), 160 * 16);
    let layer_zero = layout.backward_layers.last().unwrap();
    assert_eq!(layer_zero.final_step_eval_addresses.len(), 119);
    assert_eq!(layer_zero.extra_evaluations_addresses.len(), 15);
    assert_eq!(layout.memory_claims.end, layout.setup_claims.start);
    assert!(programs.geometry.constants <= super::super::forward::desc::PR_FWD_VM_CONST_CAP);
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
    ];
    let stage = std::env::var("M6_ABI_STAGE").unwrap_or_else(|_| "t4".to_owned());
    assert_eq!(stage, "t4", "Proth120 ABI stage is not implemented");
    rows.sort_by_key(|(symbol, _)| *symbol);
    let report = serde_json::json!({
        "schema": 1,
        "stage": stage,
        "kernels": rows.iter().map(|(symbol, bytes)| {
            assert!(*bytes > 0 && *bytes <= 32764);
            serde_json::json!({"symbol": symbol, "complete_argument_bytes": bytes, "rust_native_layout_assertions": true})
        }).collect::<Vec<_>>()
    });
    if let Ok(path) = std::env::var("M6_ABI_REPORT") {
        std::fs::write(path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    }
    println!("M6_ABI {}", report);
    println!(
        "M6_PROOF_LAYOUT bytes={} layers={}",
        layout.bytes_len(),
        layout.backward_layers.len()
    );
}
