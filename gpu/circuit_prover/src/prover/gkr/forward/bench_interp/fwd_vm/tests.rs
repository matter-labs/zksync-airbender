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

/// The three in-scope fwd-VM circuits (spec §5), in report order.
#[cfg(not(no_cuda))]
const FWD_VM_CIRCUITS: [&str; 3] = [
    "add_sub_lui_auipc_mop",
    "bigint_with_extended_control",
    "blake2_with_extended_control",
];

/// Query the three device attrs the report header records (mirrors
/// `bench_interp::tests::query_device_attrs`).
#[cfg(not(no_cuda))]
fn query_fwd_vm_device_attrs() -> super::report::FwdVmDeviceAttrs {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    let dev = get_device().unwrap();
    super::report::FwdVmDeviceAttrs {
        max_shared_memory_per_multiprocessor: device_get_attribute(
            CudaDeviceAttr::MaxSharedMemoryPerMultiprocessor,
            dev,
        )
        .unwrap(),
        max_shared_memory_per_block_optin: device_get_attribute(
            CudaDeviceAttr::MaxSharedMemoryPerBlockOptin,
            dev,
        )
        .unwrap(),
        sm_count: device_get_attribute(CudaDeviceAttr::MultiProcessorCount, dev).unwrap() as usize,
    }
}

/// Task 7 DELIVERABLE (`#[ignore]`, GPU, long: `TIMING_ITERS` × configs × layers
/// × 3 circuits). For each circuit: run the four correctness gates FIRST (via
/// `run_all_gates`, spec §7 — timing only happens after gates pass), then time
/// every (compiled layer × config) point. Flat is timed ONCE per layer (the
/// replayed production launch sum); the interpreter is timed per config
/// (`{dynamic, static-s16} × {LDC, LDG}`, `static-s16/LDG` skipped — LDC-only
/// static kernel). Both sides use the SAME capped element count
/// (`min(trace_len, TIMING_COUNT_CAP)`). Writes JSON + markdown to
/// `.agents/audits/2026-07-05-fwd-vm-ab-report.{json,md}` (GITIGNORED).
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_ab_report() {
    use super::super::harness::{time_flat, TIMING_COUNT_CAP, TIMING_ITERS};
    use super::super::fixture::CircuitFixture;
    use super::report::{FwdVmAbReport, FwdVmAbRow};
    use super::{fwd_vm_blocks_per_sm, time_fwd_vm, FwdVmConfig};
    use gkr_eval_isa::fwd::compile::layer_needs_compile;

    let device = query_fwd_vm_device_attrs();
    let mut rows: Vec<FwdVmAbRow> = Vec::new();
    let mut skips: Vec<String> = Vec::new();

    for stem in FWD_VM_CIRCUITS {
        // ── Gates FIRST (spec §7): only time layers whose four gates pass. ──
        run_all_gates(stem);

        let fixture = CircuitFixture::build(stem);
        let c = super::compile::load_fwd_vm_circuit(stem);
        let trace_len = fixture.trace_len;
        let count = trace_len.min(TIMING_COUNT_CAP);
        let capped = count < trace_len;

        for (li, layer) in c.dag.layers.iter().enumerate() {
            if !layer_needs_compile(c.sched.layers[li].order.is_empty(), layer) {
                continue;
            }
            let cl = &c.compiled.layers[li];
            let lanes = super::compile::encoded_lanes(cl);
            let n_instr = cl.program.instrs.len() as u32;
            let budget = cl.budget as u32;

            // Flat baseline: timed ONCE per layer (the interpreter's config knobs
            // do not change the flat launch sum).
            let (flat_median, flat_min, flat_launches) =
                time_flat(&fixture, li, count, TIMING_ITERS);

            for config in FwdVmConfig::ALL {
                if config.kernel_absent() {
                    skips.push(format!(
                        "{stem} L{li} {}: no static LDG kernel (corpus fits LDC; \
                         s16 LDC is the committed static form)",
                        config.label()
                    ));
                    continue;
                }
                let mut setup = super::lower::build_fwd_vm_device_setup(&fixture, &c, li);
                setup.desc.count = count as u32;

                let Some((interp_median, interp_min)) =
                    time_fwd_vm(&fixture, &setup, config, TIMING_ITERS)
                else {
                    skips.push(format!(
                        "{stem} L{li} {}: program exceeds the __constant__ array (LDC did not fit)",
                        config.label()
                    ));
                    continue;
                };

                let blocks_per_sm = fwd_vm_blocks_per_sm(config, budget).unwrap().unwrap_or(0);
                // The static-s16 kernel's cell file is a compile-time
                // `__shared__ bf cells[16 * 128]` (see FWD_VM_STATIC_BUDGET),
                // not the dynamic-smem allocation the launch requests (which
                // is 0 for static configs). Report the actual compile-time
                // footprint for static configs instead of reusing the dynamic
                // formula — it is only numerically equal to it because
                // budget == FWD_VM_STATIC_BUDGET here; a future s32
                // instantiation must not silently mis-report via this path.
                let smem_bytes = if config.is_static() {
                    super::FWD_VM_STATIC_BUDGET as usize
                        * config.threads_per_block() as usize
                        * std::mem::size_of::<crate::primitives::field::BF>()
                } else {
                    super::fwd_vm_dynamic_smem_bytes(budget, config.threads_per_block())
                };
                let interp_over_flat = if flat_median > 0.0 {
                    interp_median / flat_median
                } else {
                    f32::INFINITY
                };

                rows.push(FwdVmAbRow {
                    circuit: stem.to_string(),
                    layer: li,
                    config: config.label(),
                    variant: config.variant_name().to_string(),
                    residency: config.residency_name().to_string(),
                    tpb: config.threads_per_block(),
                    flat_median_ms: flat_median,
                    flat_min_ms: flat_min,
                    flat_launches,
                    interp_median_ms: interp_median,
                    interp_min_ms: interp_min,
                    interp_over_flat,
                    encoded_lanes: lanes.len(),
                    n_instr,
                    budget,
                    smem_bytes,
                    blocks_per_sm,
                    timed_count: count,
                    trace_len,
                    capped,
                    is_best: false, // filled by assemble()
                });
            }
        }
    }

    assert!(!rows.is_empty(), "fwd_vm_ab_report: no timed rows — vacuous");
    let report = FwdVmAbReport::assemble(device, TIMING_ITERS, TIMING_COUNT_CAP, rows, skips);
    let (md, json) = super::report::write_report(&report);
    eprintln!(
        "[fwdvm-ab-report] wrote {} rows, {} verdicts, {} skips\n  md:   {}\n  json: {}",
        report.rows.len(),
        report.verdicts.len(),
        report.skips.len(),
        md.display(),
        json.display(),
    );
}

/// ncu/nsys profiling TARGET for the fwd-VM INTERPRETER (`#[ignore]`, GPU).
/// Issues EXACTLY ONE interpreter launch — one circuit (env `FWDVM_NCU_CIRCUIT`,
/// default add_sub), layer 0, one config (env `FWDVM_NCU_CONFIG`: `dyn-ldg`,
/// `dyn-ldc`, or `static-ldc` [default]) — so an `ncu` wrapper captures a single
/// clean kernel instance (no report, no grid, no asserts on the numbers). The
/// interpreter kernel symbols are `ab_gkr_bench_fwd_vm_{ldg,ldc}_kernel` /
/// `ab_gkr_bench_fwd_vm_ldc_s16_kernel`. Mirrors
/// `bench_interp::tests::stage3_fwd_interp_ncu_target`.
///
/// ```bash
/// TEST_BINARY="$(
///   cargo test -p circuit_prover --features bench fwd_vm_interp_ncu_target \
///     --release --no-run --message-format=json \
///     | python3 .agents/bin/cargo_test_executables.py)"
/// FWDVM_NCU_CIRCUIT=add_sub_lui_auipc_mop FWDVM_NCU_CONFIG=static-ldc \
/// .agents/bin/with_gpu_lock.sh ncu \
///   --set basic --kernel-name-base demangled \
///   --kernel-name 'regex:ab_gkr_bench_fwd_vm_ldc_s16_kernel' \
///   --launch-count 1 \
///   -o "target/profiling/ncu/$(date +%Y%m%d_%H%M%S)_fwd_vm_interp" \
///   "$TEST_BINARY" \
///   --exact prover::gkr::forward::bench_interp::fwd_vm::tests::fwd_vm_interp_ncu_target \
///   --ignored --nocapture
/// ```
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_interp_ncu_target() {
    use super::super::fixture::CircuitFixture;
    use super::super::harness::TIMING_COUNT_CAP;
    use super::{time_fwd_vm, FwdVmConfig};

    let circuit =
        std::env::var("FWDVM_NCU_CIRCUIT").unwrap_or_else(|_| FWD_VM_CIRCUITS[0].to_string());
    assert!(
        FWD_VM_CIRCUITS.contains(&circuit.as_str()),
        "FWDVM_NCU_CIRCUIT={circuit} is not a fwd-VM circuit ({FWD_VM_CIRCUITS:?})"
    );
    let config = match std::env::var("FWDVM_NCU_CONFIG").as_deref() {
        Ok("dyn-ldg") => FwdVmConfig::DynamicLdg,
        Ok("dyn-ldc") => FwdVmConfig::DynamicLdc,
        Ok("static-ldc") | Err(_) => FwdVmConfig::StaticS16Ldc,
        Ok(other) => panic!("FWDVM_NCU_CONFIG={other} not in {{dyn-ldg,dyn-ldc,static-ldc}}"),
    };
    println!("ncu target: circuit {circuit} config {} (L0, one launch)", config.label());

    let fixture = CircuitFixture::build(&circuit);
    let c = super::compile::load_fwd_vm_circuit(&circuit);
    let count = fixture.trace_len.min(TIMING_COUNT_CAP);
    let mut setup = super::lower::build_fwd_vm_device_setup(&fixture, &c, 0);
    setup.desc.count = count as u32;
    // ONE launch (via a 1-iter time call — same launch path, one clean instance).
    let timed = time_fwd_vm(&fixture, &setup, config, 1);
    println!("ncu target: fwd-VM interpreter launch complete ({timed:?})");
}

/// ncu/nsys profiling TARGET for the FLAT side (`#[ignore]`, GPU). Replays ONE
/// layer's full production flat launch sequence (the interpreter's baseline) for
/// an apples-to-apples capture against `fwd_vm_interp_ncu_target`. Parameterized
/// by `FWDVM_NCU_CIRCUIT` (default add_sub); the profiled replay is wrapped in an
/// NVTX range (`fwd_vm_flat_ncu`) after a warmup, so `ncu` MUST scope to it with
/// `--nvtx --nvtx-include "fwd_vm_flat_ncu/"`. No asserts on the numbers. Mirrors
/// `bench_interp::tests::stage3_flat_fwd_ncu_target`.
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_flat_ncu_target() {
    use super::super::fixture::CircuitFixture;
    use super::super::harness::TIMING_COUNT_CAP;

    let circuit =
        std::env::var("FWDVM_NCU_CIRCUIT").unwrap_or_else(|_| FWD_VM_CIRCUITS[0].to_string());
    assert!(
        FWD_VM_CIRCUITS.contains(&circuit.as_str()),
        "FWDVM_NCU_CIRCUIT={circuit} is not a fwd-VM circuit ({FWD_VM_CIRCUITS:?})"
    );
    let fixture = CircuitFixture::build(&circuit);
    let layer_idx = 0usize;
    let count = fixture.trace_len.min(TIMING_COUNT_CAP);
    let n_launches = fixture.layers[layer_idx].replayable_launch_count();
    println!(
        "ncu flat target: circuit {circuit} L0, {n_launches} replayable flat launches \
         (build pass + warmup precede the profiled NVTX range `fwd_vm_flat_ncu`)"
    );

    // Warmup OUTSIDE the profiled range.
    fixture.replay_layer_count(layer_idx, count).unwrap();
    fixture.context().get_exec_stream().synchronize().unwrap();

    // Profiled replay INSIDE the NVTX range.
    {
        let _range = crate::primitives::nvtx::scoped_range(None, "fwd_vm_flat_ncu");
        fixture.replay_layer_count(layer_idx, count).unwrap();
        fixture.context().get_exec_stream().synchronize().unwrap();
    }
    println!("ncu flat target: profiled replay complete ({n_launches} flat launches)");
}
