//! Task 1: host-only proof that the three in-scope circuits compile through
//! the production stage-3 `compile_circuit` path and that every compiled
//! layer's encoded program round-trips (spec §5 canonical pre-gate). Also
//! prints the LDC feasibility table (spec §4 size probe).
//!
//! Task 6: the four semantic gates (G-PTR → G-CPU → G-DEV → G-ALIAS, spec §7)
//! are factored into `run_all_gates(stem)` and driven by one `#[test]` per
//! circuit so failures are attributable to a circuit.

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

/// The full fwd-VM gate suite for one circuit, run in spec §7 order:
/// G-PTR → G-CPU → G-DEV → G-ALIAS, over every compiled layer, both
/// residencies where the program fits the LDC constant array.
///
/// - **G-PTR**: every column-table read pointer equals the independently
///   re-derived storage_column pointer; every materialized pair has a
///   non-null, interp-owned (NOT storage) write pointer; specials pointers
///   match their re-derived sources; capacity asserts fire on overflow.
/// - **G-CPU**: CPU fwd-VM interpreter on D2H real data == D2H flat outputs,
///   sampled rows, every non-skipped root (plus the SP2 differential pre-gate).
/// - **G-DEV + G-ALIAS**: device interpreter bit-exact vs flat, all rows,
///   every compiled layer, both residencies where the program fits LDC.
#[cfg(not(no_cuda))]
fn run_all_gates(stem: &str) {
    use super::lower::{assert_gptr, build_fwd_vm_device_setup, run_gdev_layer};
    use super::resolvers::{sample_rows, HostSnapshot, HostStorageResolvers};
    use crate::prover::gkr::forward::bench_interp::fixture::CircuitFixture;
    use gkr_eval_isa::fwd::compile::layer_needs_compile;
    use gkr_eval_isa::fwd::interp::interpret_layer_row_with_peeks;

    let fixture = CircuitFixture::build(stem);
    let c = super::compile::load_fwd_vm_circuit(stem);

    let mut layers_gated = 0usize;
    let mut cpu_checks = 0usize;
    for (li, layer) in c.dag.layers.iter().enumerate() {
        if !layer_needs_compile(c.sched.layers[li].order.is_empty(), layer) {
            continue;
        }
        let cl = &c.compiled.layers[li];

        // ── G-PTR: structural pointer re-derivation. ──
        let setup = build_fwd_vm_device_setup(&fixture, &c, li);
        assert_gptr(&fixture, &c, li, &setup);
        drop(setup);

        // ── G-CPU: CPU fwd-VM on real data == flat, sampled rows. ──
        let snap = HostSnapshot::capture_for_layer(&fixture, cl, layer);
        let host = HostStorageResolvers::new(&snap, &fixture);
        let r = host.resolvers();
        let rows = sample_rows(fixture.trace_len);
        // SP2 differential pre-gate on real data (spec §6):
        super::resolvers::validate_bindings_sampled(cl, layer, &host, &r, &rows);
        for &row in &rows {
            let outs = interpret_layer_row_with_peeks(cl, layer, &r, &host, row)
                .unwrap_or_else(|e| panic!("{stem} L{li} row {row}: {e:?}"));
            for (rid, out) in &cl.root_outputs {
                let want = snap.flat_root_value(&fixture, &c, li, *rid, out, row);
                assert_eq!(outs.by_root[rid], want, "{stem} L{li} root {rid:?} row {row}");
                cpu_checks += 1;
            }
        }

        // ── G-DEV + G-ALIAS: device interp bit-exact vs flat, all rows. ──
        run_gdev_layer(&fixture, &c, li).unwrap_or_else(|e| panic!("{stem} L{li}: {e}"));

        layers_gated += 1;
    }
    assert!(layers_gated > 0, "{stem}: no compiled layers gated — vacuous");
    assert!(cpu_checks > 0, "{stem}: no G-CPU root checks — vacuous");
    eprintln!("[fwdvm-gates] {stem}: {layers_gated} layers gated, {cpu_checks} G-CPU root checks");
}

#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_gates_add_sub() {
    run_all_gates("add_sub_lui_auipc_mop");
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_gates_bigint() {
    run_all_gates("bigint_with_extended_control");
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_gates_blake2() {
    run_all_gates("blake2_with_extended_control");
}
