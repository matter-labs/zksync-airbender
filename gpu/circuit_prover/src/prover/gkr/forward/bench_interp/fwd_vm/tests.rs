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

// G-CPU (spec §7): CPU fwd-VM interpreter on D2H real data == D2H flat outputs,
// sampled rows, every non-skipped root, every compiled add_sub layer.
// First-ever real-data run of the fwd VM.
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_gcpu_add_sub() {
    use super::resolvers::{sample_rows, HostSnapshot, HostStorageResolvers};
    use crate::prover::gkr::forward::bench_interp::fixture::CircuitFixture;
    use gkr_eval_isa::fwd::compile::layer_needs_compile;
    use gkr_eval_isa::fwd::interp::interpret_layer_row_with_peeks;

    let fixture = CircuitFixture::build("add_sub_lui_auipc_mop");
    let c = super::compile::load_fwd_vm_circuit("add_sub_lui_auipc_mop");
    let mut checks = 0usize;
    for (li, layer) in c.dag.layers.iter().enumerate() {
        if !layer_needs_compile(c.sched.layers[li].order.is_empty(), layer) {
            continue;
        }
        let cl = &c.compiled.layers[li];
        let snap = HostSnapshot::capture_for_layer(&fixture, cl, layer);
        let host = HostStorageResolvers::new(&snap, &fixture);
        let r = host.resolvers();
        // SP2 differential pre-gate on real data (spec §6):
        super::resolvers::validate_bindings_sampled(
            cl,
            layer,
            &host,
            &r,
            &sample_rows(fixture.trace_len),
        );
        for &row in &sample_rows(fixture.trace_len) {
            let outs = interpret_layer_row_with_peeks(cl, layer, &r, &host, row)
                .unwrap_or_else(|e| panic!("L{li} row {row}: {e:?}"));
            for (rid, out) in &cl.root_outputs {
                let want = snap.flat_root_value(&fixture, &c, li, *rid, out, row);
                assert_eq!(outs.by_root[rid], want, "L{li} root {rid:?} row {row}");
                checks += 1;
            }
        }
    }
    assert!(checks > 0, "vacuous");
}

// G-PTR (spec §7): every column-table read pointer equals the independently
// re-derived storage_column pointer; every materialized pair has a non-null,
// interp-owned (NOT storage) write pointer; specials pointers match their
// re-derived sources; capacity asserts fire on overflow, never truncate.
#[test]
#[ignore]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_gptr_add_sub() {
    use crate::prover::gkr::forward::bench_interp::fixture::CircuitFixture;
    use gkr_eval_isa::fwd::compile::layer_needs_compile;
    use super::lower::build_fwd_vm_device_setup;

    let fixture = CircuitFixture::build("add_sub_lui_auipc_mop");
    let c = super::compile::load_fwd_vm_circuit("add_sub_lui_auipc_mop");
    for (li, layer) in c.dag.layers.iter().enumerate() {
        if !layer_needs_compile(c.sched.layers[li].order.is_empty(), layer) {
            continue;
        }
        let setup = build_fwd_vm_device_setup(&fixture, &c, li);
        super::lower::assert_gptr(&fixture, &c, li, &setup); // re-derivation compare
    }
}
