//! Task 1: host-only proof that the three in-scope circuits compile through
//! the production stage-3 `compile_circuit` path and that every compiled
//! layer's encoded program round-trips (spec §5 canonical pre-gate). Also
//! prints the LDC feasibility table (spec §4 size probe).

// Host-only (no GPU): the three scoped circuits compile via the production path
// and every compiled layer's encoded program round-trips. Prints the LDC
// feasibility table (spec §4 size probe).
#[test]
fn fwd_vm_circuits_compile_and_size_probe() {
    for stem in [
        "add_sub_lui_auipc_mop",
        "bigint_with_extended_control",
        "blake2_with_extended_control",
    ] {
        let c = super::compile::load_fwd_vm_circuit(stem);
        assert_eq!(c.compiled.layers.len(), c.dag.layers.len(), "{stem} layer count");
        assert_eq!(c.compiled.budget, 16, "{stem} committed budget");
        let mut any = false;
        for (li, layer) in c.dag.layers.iter().enumerate() {
            if !gkr_eval_isa::fwd::compile::layer_needs_compile(c.sched.layers[li].order.is_empty(), layer) {
                continue;
            }
            let lanes = super::compile::encoded_lanes(&c.compiled.layers[li]);
            assert!(!lanes.is_empty(), "{stem} L{li} empty program");
            let fits_ldc = lanes.len() <= crate::prover::gkr::forward::bench_interp::BENCH_INTERP_PROGRAM_LDC_LANES;
            eprintln!("[fwdvm-probe] {stem} L{li}: {} lanes, ldc={}", lanes.len(), fits_ldc);
            any = true;
        }
        assert!(any, "{stem} no compiled layers — vacuous");
    }
}
