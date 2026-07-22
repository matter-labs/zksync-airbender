//! Task 1: host-only proof that the three in-scope circuits compile through
//! the production stage-3 `compile_circuit` path and that every compiled
//! layer's encoded program round-trips (spec §5 canonical pre-gate). Also
//! prints the LDC feasibility table (spec §4 size probe).
//!
//! The v1 four-gate suite (G-PTR → G-CPU → G-DEV → G-ALIAS) that used to live
//! here is gone (Task 12) — superseded by the Task 10 production v2 parity
//! gate (`vm::gpu_tests::run_vm_parity`, exercised via `fwd_vm_v2_parity_*`
//! and reused below by `fwd_vm_ab_report`).

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
            if !gkr_eval_isa::fwd::compile::layer_needs_compile(c.sched.layers[li].units.is_empty(), layer) {
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

/// Task 11 DELIVERABLE (`#[ignore]`, GPU, long: `TIMING_ITERS` × layers × 3
/// circuits): the fwd-VM A/B over the PRODUCTION v2 path. For each circuit:
/// run the Task-10 v2 parity gate FIRST (`run_vm_parity` — VALIDATE + release
/// kernels bit-exact vs the flat oracle; timing only happens after the gate
/// passes), then per compiled layer time the flat replay (unchanged baseline
/// arm) against ONE launch of the RELEASE `ab_gkr_fwd_vm_s4_kernel`, lowered
/// via the production `lower_layer_desc` over the real consolidated-storage
/// resolver. Both sides use the SAME capped element count
/// (`min(trace_len, TIMING_COUNT_CAP)`). Report name + shape are kept from the
/// Task-7 v1 bench (one row per (circuit, layer, config); the config column
/// now carries the single `v2-s4/inline` production point) so cross-history
/// comparisons stay valid. Writes JSON + markdown to
/// `.agents/audits/2026-07-05-fwd-vm-ab-report.{json,md}` (GITIGNORED).
#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn fwd_vm_ab_report() {
    use era_cudart::memory::memory_copy_async;
    use gkr_eval_isa::fwd::compile::layer_needs_compile;

    use super::super::fixture::CircuitFixture;
    use super::super::harness::{time_flat, time_iters, TIMING_COUNT_CAP, TIMING_ITERS};
    use super::report::{FwdVmAbReport, FwdVmAbRow};
    use crate::allocator::tracker::AllocationPlacement;
    use crate::primitives::context::DeviceAllocation;
    use crate::prover::gkr::forward::vm::gpu_tests::{
        build_header, const_derived_e4_values, resolve_storage_column, run_vm_parity,
    };
    use crate::prover::gkr::forward::vm::lower::lower_layer_desc;
    use crate::prover::gkr::forward::vm::{
        fwd_vm_s4_blocks_per_sm, launch_fwd_vm_s4, launch_fwd_vm_validate,
        upload_const_derived_e4, FWD_VM_S4_BUDGET_LANES, FWD_VM_THREADS_PER_BLOCK,
    };

    let device = query_fwd_vm_device_attrs();
    let mut rows: Vec<FwdVmAbRow> = Vec::new();
    let skips: Vec<String> = Vec::new();

    // Release-kernel context, config-independent: static smem (zero dynamic
    // bytes at launch; the compile-time `__shared__` cell file is already
    // accounted for by ptxas, so the occupancy API reflects it automatically).
    let blocks_per_sm = fwd_vm_s4_blocks_per_sm().unwrap();
    let smem_bytes = FWD_VM_S4_BUDGET_LANES as usize
        * FWD_VM_THREADS_PER_BLOCK as usize
        * std::mem::size_of::<crate::primitives::field::BF>();

    for stem in FWD_VM_CIRCUITS {
        // ── Gate FIRST: the Task-10 v2 parity gate (validate + release
        // kernels bit-exact vs the flat oracle, every compiled layer). ──
        run_vm_parity(stem);

        let fixture = CircuitFixture::build(stem);
        let c = super::compile::load_fwd_vm_circuit(stem);
        let context = fixture.context();
        let header = build_header(&fixture);
        let trace_len = fixture.trace_len;
        let count = trace_len.min(TIMING_COUNT_CAP);
        let capped = count < trace_len;

        for (li, layer) in c.dag.layers.iter().enumerate() {
            if !layer_needs_compile(c.sched.layers[li].units.is_empty(), layer) {
                continue;
            }
            let cl = &c.compiled.layers[li];
            let n_instr = cl.program.instrs.len() as u32;
            let budget = cl.budget as u32;

            // Flat baseline: unchanged from the Task-7 report (the replayed
            // production forward launch sum at the capped count).
            let (flat_median, flat_min, flat_launches) =
                time_flat(&fixture, li, count, TIMING_ITERS);

            // Production v2 lowering against the real consolidated storage
            // (the exact Task-10 gate plumbing).
            let resolve = |addr| resolve_storage_column(&fixture, addr);
            let challenge = |r: &_| super::resolvers::challenge_value(&fixture, r);
            let mut setup = lower_layer_desc(cl, &header, &resolve, &challenge, None)
                .unwrap_or_else(|e| panic!("{stem} L{li}: lower_layer_desc: {e:?}"));
            assert!(
                setup.desc.program_ldg.is_null(),
                "{stem} L{li}: corpus program unexpectedly overflowed the inline cap"
            );
            upload_const_derived_e4(&const_derived_e4_values(&fixture, cl), context)
                .unwrap_or_else(|e| panic!("{stem} L{li}: const-derived-e4 upload: {e:?}"));

            // Fail-closed pre-check at FULL trace_len (desc.count is also the
            // mapping-arena column stride, so the structural checks must run
            // uncapped): one VALIDATE launch, error_flag must stay 0 — a
            // broken kernel must not silently yield a timing number.
            let mut err_dev: DeviceAllocation<u32> =
                context.alloc(1, AllocationPlacement::Top).unwrap();
            memory_copy_async(&mut err_dev[0..1], &[0u32], context.get_exec_stream()).unwrap();
            launch_fwd_vm_validate(&setup, budget, err_dev.as_mut_ptr(), context)
                .unwrap_or_else(|e| panic!("{stem} L{li}: validate launch: {e:?}"));
            let mut err = [0u32];
            memory_copy_async(&mut err, &err_dev[0..1], context.get_exec_stream()).unwrap();
            context.get_exec_stream().synchronize().unwrap();
            assert_eq!(
                err[0], 0,
                "{stem} L{li}: VALIDATE kernel error_flag = {:#x} — timing would be meaningless",
                err[0]
            );

            // Timed loop: the RELEASE s4 kernel at the capped count. For a
            // capped circuit the mapping-arena column stride (= desc.count)
            // then under-reads the arenas' true stride (= trace_len): peek
            // VALUES land on other rows of the same arena, but the load
            // count/coalescing shape is identical, so the TIMING is
            // representative — correctness is proven separately by the
            // uncapped gate + pre-check above. The flat arm has the same
            // property (replay at a capped count over full-stride columns).
            setup.desc.count = count as u32;
            let (interp_median, interp_min) =
                time_iters(context.get_exec_stream(), TIMING_ITERS, || {
                    launch_fwd_vm_s4(&setup, budget, context).unwrap();
                });

            let interp_over_flat = if flat_median > 0.0 {
                interp_median / flat_median
            } else {
                f32::INFINITY
            };

            rows.push(FwdVmAbRow {
                circuit: stem.to_string(),
                layer: li,
                config: "v2-s4/inline".to_string(),
                variant: "v2-s4".to_string(),
                residency: "inline".to_string(),
                tpb: FWD_VM_THREADS_PER_BLOCK,
                flat_median_ms: flat_median,
                flat_min_ms: flat_min,
                flat_launches,
                interp_median_ms: interp_median,
                interp_min_ms: interp_min,
                interp_over_flat,
                encoded_lanes: setup.desc.program_lanes as usize,
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

/// ncu/nsys profiling TARGET for the PRODUCTION v2 fwd-VM interpreter
/// (`#[ignore]`, GPU). Issues EXACTLY ONE release-kernel launch — one circuit
/// (env `FWDVM_NCU_CIRCUIT`, default add_sub), one layer (env `FWDVM_NCU_LAYER`,
/// default 0) — so an `ncu` wrapper captures a single clean instance of
/// `ab_gkr_fwd_vm_s4_kernel` (no report, no grid, no asserts on the numbers).
///
/// ```bash
/// TEST_BINARY="$(
///   cargo test -p circuit_prover --features bench fwd_vm_interp_ncu_target \
///     --release --no-run --message-format=json \
///     | python3 .agents/bin/cargo_test_executables.py)"
/// FWDVM_NCU_CIRCUIT=add_sub_lui_auipc_mop \
/// .agents/bin/with_gpu_lock.sh ncu \
///   --set basic --kernel-name-base demangled \
///   --kernel-name 'regex:ab_gkr_fwd_vm_s4_kernel' \
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
    use crate::prover::gkr::forward::vm::gpu_tests::{
        build_header, const_derived_e4_values, resolve_storage_column,
    };
    use crate::prover::gkr::forward::vm::lower::lower_layer_desc;
    use crate::prover::gkr::forward::vm::{launch_fwd_vm_s4, upload_const_derived_e4};

    let circuit =
        std::env::var("FWDVM_NCU_CIRCUIT").unwrap_or_else(|_| FWD_VM_CIRCUITS[0].to_string());
    assert!(
        FWD_VM_CIRCUITS.contains(&circuit.as_str()),
        "FWDVM_NCU_CIRCUIT={circuit} is not a fwd-VM circuit ({FWD_VM_CIRCUITS:?})"
    );
    let layer_idx: usize = std::env::var("FWDVM_NCU_LAYER")
        .map(|s| s.parse().expect("FWDVM_NCU_LAYER must be a layer index"))
        .unwrap_or(0);
    println!("ncu target: circuit {circuit} L{layer_idx} v2-s4 (one launch)");

    let fixture = CircuitFixture::build(&circuit);
    let c = super::compile::load_fwd_vm_circuit(&circuit);
    let context = fixture.context();
    let header = build_header(&fixture);
    let cl = &c.compiled.layers[layer_idx];
    let resolve = |addr| resolve_storage_column(&fixture, addr);
    let challenge = |r: &_| super::resolvers::challenge_value(&fixture, r);
    let mut setup = lower_layer_desc(cl, &header, &resolve, &challenge, None).unwrap();
    upload_const_derived_e4(&const_derived_e4_values(&fixture, cl), context).unwrap();
    // Env-gated full-domain override for docs-compliant ncu captures: profile
    // the circuit's REAL trace_len (the fixture already allocates full-trace
    // storage). Default keeps the A/B timing cap for cross-history parity.
    let count = if std::env::var("FWDVM_NCU_FULL_TRACE").is_ok() {
        fixture.trace_len
    } else {
        fixture.trace_len.min(TIMING_COUNT_CAP)
    };
    println!("ncu target: count = {count} (trace_len = {})", fixture.trace_len);
    setup.desc.count = count as u32;
    launch_fwd_vm_s4(&setup, cl.budget as u32, context).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    println!("ncu target: v2 fwd-VM release launch complete");
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
