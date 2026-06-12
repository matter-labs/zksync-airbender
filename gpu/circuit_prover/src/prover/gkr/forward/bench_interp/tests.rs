use super::lower::{lower_program, output_widths, LoweredProgram};
use super::{
    launch_bench_fwd_interp, upload_bench_program_to_constant, InterpDesc, InterpResidency,
};

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::BF;
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;

use era_cudart::memory::memory_copy_async;
use field::Field;
use serial_test::serial;

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn bench_stub_kernel_roundtrip() {
    use super::launch_bench_fwd_interp_smoke;

    let context = make_test_context(256, 32);
    let count = 256usize;
    let values = (0..count as u32).map(BF::new).collect::<Vec<_>>();

    let mut src_dev = context.alloc(count, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut src_dev, &values, context.get_exec_stream()).unwrap();
    let mut dst_dev = context.alloc(count, AllocationPlacement::Top).unwrap();

    launch_bench_fwd_interp_smoke(src_dev.as_ptr(), dst_dev.as_mut_ptr(), count, &context).unwrap();

    let mut host = vec![BF::ZERO; count];
    memory_copy_async(&mut host, &dst_dev, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(host, values);
}

// ---------------------------------------------------------------------------
// Task 3: GPU↔CPU interpreter parity on synthetic staged sources.
// NativeK payload routines are SKIPPED by the kernel (counted), but the
// CacheK Dst::Slot sentinel write is replicated with ZERO; CPU cache
// sentinels are forced to ZERO so both sides agree by construction.
// ---------------------------------------------------------------------------

use gkr_design_space::import::load_circuit;
use gkr_eval_isa::compiler::fwd::{compile_forward, CompiledForward, FwdParams};
use gkr_eval_isa::eval_ref::{random_row, Bf, Ext};
use gkr_eval_isa::interp::{execute, ExecResult, StagedSources};
use gkr_eval_isa::isa::Op;
use rand::{rngs::StdRng, SeedableRng};
use std::panic::{catch_unwind, AssertUnwindSafe};

const PARITY_TRACE_LEN: usize = 1024;

/// Replicated from gkr_eval_isa/tests/oracle_forward_native.rs:35-40 (Task 6
/// of the stage-3 plan consolidates both copies into a test_support module).
fn base_part(v: Ext) -> Bf {
    use field::FieldExtension;
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    assert!(
        coeffs[1..].iter().all(|c| c.is_zero()),
        "bf source holds non-base value"
    );
    coeffs[0]
}

fn alloc_upload<T>(context: &ProverContext, host: &[T]) -> DeviceAllocation<T> {
    let mut dev: DeviceAllocation<T> = context
        .alloc(host.len().max(1), AllocationPlacement::Top)
        .unwrap();
    if !host.is_empty() {
        memory_copy_async(&mut dev[0..host.len()], host, context.get_exec_stream()).unwrap();
    }
    dev
}

struct ParityPoint<'a> {
    context: &'a ProverContext,
    label: String,
    cf: CompiledForward,
    cpu: ExecResult,
    lowered: LoweredProgram,
    // Device allocations backing the lowered pointers (kept alive for the
    // duration of the launches; test code, synchronous by design).
    _src_bf_dev: DeviceAllocation<Bf>,
    _src_e4_dev: DeviceAllocation<Ext>,
    out_bf_dev: DeviceAllocation<Bf>,
    out_e4_dev: DeviceAllocation<Ext>,
    /// (slot j, e4, column index within the bf/e4 output buffer).
    out_slots: Vec<(u16, bool, usize)>,
    lanes_dev: DeviceAllocation<u16>,
    consts_dev: DeviceAllocation<BF>,
    sources_tbl_dev: DeviceAllocation<u64>,
    outputs_tbl_dev: DeviceAllocation<u64>,
    output_e4_dev: DeviceAllocation<u32>,
    /// [native_skip, error_flag].
    debug_dev: DeviceAllocation<u32>,
    /// Final cell-file dump, layout [c * t + row], budget_cells x t.
    debug_cells_dev: DeviceAllocation<Bf>,
}

fn build_parity_point<'a>(
    context: &'a ProverContext,
    label: String,
    layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    cf: CompiledForward,
    seed: u64,
) -> ParityPoint<'a> {
    let t = PARITY_TRACE_LEN;
    let mut rng = StdRng::seed_from_u64(seed);

    // CPU reference: random staged row, ALL cache sentinels zero (the GPU
    // skips NativeK entirely, leaving the zero-initialized cells in place).
    let row = random_row(&layer.arena.nodes, &mut rng);
    let src = StagedSources {
        bf: cf
            .source_map
            .bf
            .iter()
            .map(|&n| base_part(row.leaf_vals[n].unwrap()))
            .collect(),
        e4: cf
            .source_map
            .e4
            .iter()
            .map(|&n| row.leaf_vals[n].unwrap())
            .collect(),
        cache_outs: vec![Ext::ZERO; layer.caches.len()],
    };
    let cpu = execute(&cf.program, &src);

    // GPU staging: every row of a source column holds the same staged value.
    let mut bf_host = vec![Bf::ZERO; src.bf.len() * t];
    for (i, &v) in src.bf.iter().enumerate() {
        bf_host[i * t..(i + 1) * t].fill(v);
    }
    let mut e4_host = vec![Ext::ZERO; src.e4.len() * t];
    for (i, &v) in src.e4.iter().enumerate() {
        e4_host[i * t..(i + 1) * t].fill(v);
    }
    let src_bf_dev = alloc_upload(context, &bf_host);
    let src_e4_dev = alloc_upload(context, &e4_host);

    // Output columns, zeroed, packed per width; slot -> column index.
    let widths = output_widths(&cf.program);
    let mut out_slots = Vec::new();
    let (mut n_out_bf, mut n_out_e4) = (0usize, 0usize);
    for &(j, _node) in &cf.outputs {
        let e4 = widths[j as usize].expect("cf.outputs slot never written");
        let col = if e4 { &mut n_out_e4 } else { &mut n_out_bf };
        out_slots.push((j, e4, *col));
        *col += 1;
    }
    let out_bf_dev = alloc_upload(context, &vec![Bf::ZERO; n_out_bf * t]);
    let out_e4_dev = alloc_upload(context, &vec![Ext::ZERO; n_out_e4 * t]);

    let lowered = lower_program(
        &cf,
        |i| unsafe { src_bf_dev.as_ptr().add(i * t) } as *const u8,
        |i| unsafe { src_e4_dev.as_ptr().add(i * t) } as *const u8,
        |j| {
            let (_, e4, col) = *out_slots
                .iter()
                .find(|&&(jj, ..)| jj == j)
                .expect("unknown output slot");
            let ptr = if e4 {
                (unsafe { out_e4_dev.as_ptr().add(col * t) }) as *mut u8
            } else {
                (unsafe { out_bf_dev.as_ptr().add(col * t) }) as *mut u8
            };
            (ptr, e4)
        },
    );

    let lanes_dev = alloc_upload(context, &lowered.lanes);
    let consts_dev = alloc_upload(context, &lowered.consts);
    let sources_host: Vec<u64> = lowered.source_ptrs.iter().map(|&p| p as u64).collect();
    let sources_tbl_dev = alloc_upload(context, &sources_host);
    let outputs_host: Vec<u64> = lowered.output_ptrs.iter().map(|&p| p as u64).collect();
    let outputs_tbl_dev = alloc_upload(context, &outputs_host);
    let output_e4_dev = alloc_upload(context, &lowered.output_e4);
    let debug_dev = alloc_upload(context, &[0u32; 2][..]);
    let debug_cells_dev = alloc_upload(context, &vec![Bf::ZERO; lowered.budget_cells as usize * t]);

    ParityPoint {
        context,
        label,
        cf,
        cpu,
        lowered,
        _src_bf_dev: src_bf_dev,
        _src_e4_dev: src_e4_dev,
        out_bf_dev,
        out_e4_dev,
        out_slots,
        lanes_dev,
        consts_dev,
        sources_tbl_dev,
        outputs_tbl_dev,
        output_e4_dev,
        debug_dev,
        debug_cells_dev,
    }
}

impl ParityPoint<'_> {
    fn run_and_check(&mut self, residency: InterpResidency) {
        let context = self.context;
        let t = PARITY_TRACE_LEN;
        let label = format!("{} [{:?}]", self.label, residency);

        // Reset outputs + debug counters (the LDC pass reruns on the same
        // buffers; a stale value passing the compare would prove nothing).
        let n_out_bf: usize = self.out_slots.iter().filter(|s| !s.1).count();
        let n_out_e4: usize = self.out_slots.iter().filter(|s| s.1).count();
        if n_out_bf > 0 {
            memory_copy_async(
                &mut self.out_bf_dev[0..n_out_bf * t],
                &vec![Bf::ZERO; n_out_bf * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        if n_out_e4 > 0 {
            memory_copy_async(
                &mut self.out_e4_dev[0..n_out_e4 * t],
                &vec![Ext::ZERO; n_out_e4 * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        memory_copy_async(
            &mut self.debug_dev,
            &[0u32; 2][..],
            context.get_exec_stream(),
        )
        .unwrap();
        let n_cells = self.lowered.budget_cells as usize;
        memory_copy_async(
            &mut self.debug_cells_dev,
            &vec![Bf::ZERO; n_cells * t],
            context.get_exec_stream(),
        )
        .unwrap();

        let program_ldg = match residency {
            InterpResidency::Ldg => self.lanes_dev.as_ptr(),
            InterpResidency::Ldc => std::ptr::null(),
        };
        let desc = InterpDesc {
            program_ldg,
            program_lanes: self.lowered.lanes.len() as u32,
            n_instr: self.lowered.n_instr,
            sources: self.sources_tbl_dev.as_ptr() as *const *const u8,
            n_sources_bf: self.lowered.n_sources_bf,
            outputs: self.outputs_tbl_dev.as_ptr() as *const *mut u8,
            output_e4: self.output_e4_dev.as_ptr(),
            consts: self.consts_dev.as_ptr(),
            budget_cells: self.lowered.budget_cells,
            count: t as u32,
            native_skip: self.debug_dev.as_mut_ptr(),
            error_flag: unsafe { self.debug_dev.as_mut_ptr().add(1) },
            debug_cells: self.debug_cells_dev.as_mut_ptr() as *mut BF,
        };
        launch_bench_fwd_interp(&desc, residency, context).unwrap();

        let mut out_bf_host = vec![Bf::ZERO; n_out_bf * t];
        if n_out_bf > 0 {
            memory_copy_async(
                &mut out_bf_host,
                &self.out_bf_dev[0..n_out_bf * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let mut out_e4_host = vec![Ext::ZERO; n_out_e4 * t];
        if n_out_e4 > 0 {
            memory_copy_async(
                &mut out_e4_host,
                &self.out_e4_dev[0..n_out_e4 * t],
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let mut cells_host = vec![Bf::ZERO; n_cells * t];
        memory_copy_async(
            &mut cells_host,
            &self.debug_cells_dev,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut debug_host = [0u32; 2];
        memory_copy_async(
            &mut debug_host[..],
            &self.debug_dev,
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        assert_eq!(debug_host[1], 0, "{label}: kernel reported INTERP_ERR bits");

        // NativeK skip accounting: once per (NativeK instruction, active thread).
        let n_native = self
            .cf
            .program
            .instrs
            .iter()
            .filter(|i| i.op == Op::NativeK)
            .count() as u32;
        assert_eq!(
            debug_host[0],
            n_native * t as u32,
            "{label}: native_skip counter (expected {n_native} NativeK x {t} threads)"
        );

        // Cell-file parity: the kernel dumps its FINAL smem cell file; compare
        // against the CPU interpreter's final slot file for every cell. This
        // exercises the value path even when cf.outputs is empty.
        assert_eq!(
            self.cpu.final_cells.len(),
            n_cells,
            "{label}: CPU cell-file length vs lowered budget_cells"
        );
        for row in [0usize, t - 1] {
            for c in 0..n_cells {
                assert_eq!(
                    cells_host[c * t + row],
                    self.cpu.final_cells[c],
                    "{label}: cell {c} row {row}"
                );
            }
        }

        // Outputs: rows 0 and t-1 must equal the CPU interpreter's result.
        for &(j, e4, col) in &self.out_slots {
            let cpu_v = self.cpu.outputs[j as usize]
                .unwrap_or_else(|| panic!("{label}: CPU never wrote output {j}"));
            for row in [0usize, t - 1] {
                if e4 {
                    let gpu_v = out_e4_host[col * t + row];
                    assert_eq!(gpu_v, cpu_v, "{label}: e4 output {j} row {row}");
                } else {
                    let gpu_v = out_bf_host[col * t + row];
                    assert_eq!(gpu_v, base_part(cpu_v), "{label}: bf output {j} row {row}");
                }
            }
        }
        // Slots absent from cf.outputs are never written on either side: the
        // lowering left them null (and asserts the program agrees); the CPU
        // result must be None for them.
        for (j, v) in self.cpu.outputs.iter().enumerate() {
            if !self.out_slots.iter().any(|&(jj, ..)| jj as usize == j) {
                assert!(
                    v.is_none(),
                    "{label}: CPU wrote output {j} the lowering skipped"
                );
            }
        }
    }
}

#[test]
#[ignore] // GPU; run via .agents/bin/with_gpu_lock.sh (see .agents/gpu_work.md)
#[cfg(not(no_cuda))]
#[serial]
fn interp_core_parity() {
    let context = make_test_context(256, 32);
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for (ci, circuit) in ["add_sub_lui_auipc_mop", "blake2_with_extended_control"]
        .into_iter()
        .enumerate()
    {
        let c = load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json"))).unwrap();
        let layer = &c.circuit.layers[0];
        let graph = &c.graphs[0];
        let mut compiled_any = false;
        for budget in [32usize, 64] {
            let params = FwdParams {
                budget_cells: budget,
                leaf_cache: true,
                exclude_max_quadratic: false,
            };
            // Tight budgets can be GENUINELY infeasible (mandatory cache-cell
            // operands exceeding the budget) — skip with a recorded marker.
            let cf = match catch_unwind(AssertUnwindSafe(|| compile_forward(layer, graph, params)))
            {
                Ok(cf) => cf,
                Err(_) => {
                    println!("SKIP {circuit} L0 budget {budget}: compile_forward infeasible");
                    continue;
                }
            };
            compiled_any = true;
            let label = format!("{circuit} L0 budget {budget}");
            let seed = 0x57A6_E3u64 ^ ((ci as u64) << 32) ^ budget as u64;
            let mut point = build_parity_point(&context, label.clone(), layer, cf, seed);
            point.run_and_check(InterpResidency::Ldg);
            if upload_bench_program_to_constant(&point.lowered.lanes).unwrap() {
                point.run_and_check(InterpResidency::Ldc);
            } else {
                println!(
                    "SKIP {label} LDC: program {} lanes exceeds the 28KB constant array",
                    point.lowered.lanes.len()
                );
            }
        }
        assert!(
            compiled_any,
            "{circuit}: no budget compiled — spurious-panic check"
        );
    }
}
