//! fwd-VM program acquisition (Task 1, host-only) for the planned CUDA
//! interpreter over `gkr_eval_isa` fwd-VM `CompiledCircuit` programs.
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))` (inherited from
//! `bench_interp`, see `bench_interp/mod.rs`). No production wiring.

pub(crate) mod compile;
pub(crate) mod lower;
pub(crate) mod report;
pub(crate) mod resolvers;
mod tests;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use self::lower::{FwdVmDeviceSetup, InterpDesc3};
use super::fixture::CircuitFixture;
use super::{
    upload_bench_program_to_constant, InterpResidency, BENCH_INTERP_DEFAULT_SMEM_CAP,
    BENCH_INTERP_THREADS_PER_BLOCK,
};
use crate::prover::ProverContext;

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBenchFwdVm,
    desc: InterpDesc3,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_vm_ldg_kernel(desc: InterpDesc3)
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_vm_ldc_kernel(desc: InterpDesc3)
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_vm_ldc_s16_kernel(desc: InterpDesc3)
);

/// The committed static-smem cell budget (`ab_gkr_bench_fwd_vm_ldc_s16_kernel`'s
/// compile-time `__shared__ bf cells[16 * 128]`). The corpus compiled budget is
/// 16 (asserted per fixture), and every corpus program fits the `__constant__`
/// array, so an s16 LDC variant is the right static form.
pub(crate) const FWD_VM_STATIC_BUDGET: u32 = 16;

/// One cell of the Task-7 A/B config matrix: `{dynamic, static-s16} × {LDC,
/// LDG}`. The static-s16 kernel is instantiated LDC-only (spec: every corpus
/// program fits the `__constant__` array), so `StaticS16Ldg` has NO kernel —
/// `kernel()` returns `None`, `time_fwd_vm`/`fwd_vm_blocks_per_sm` return
/// `None`, and the report records it as a skip.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FwdVmConfig {
    DynamicLdg,
    DynamicLdc,
    StaticS16Ldc,
    StaticS16Ldg,
}

impl FwdVmConfig {
    /// The full 4-cell matrix, enumerated in report order.
    pub(crate) const ALL: [FwdVmConfig; 4] = [
        FwdVmConfig::DynamicLdg,
        FwdVmConfig::DynamicLdc,
        FwdVmConfig::StaticS16Ldc,
        FwdVmConfig::StaticS16Ldg,
    ];

    pub(crate) fn residency(self) -> InterpResidency {
        match self {
            FwdVmConfig::DynamicLdg | FwdVmConfig::StaticS16Ldg => InterpResidency::Ldg,
            FwdVmConfig::DynamicLdc | FwdVmConfig::StaticS16Ldc => InterpResidency::Ldc,
        }
    }

    pub(crate) fn is_static(self) -> bool {
        matches!(self, FwdVmConfig::StaticS16Ldc | FwdVmConfig::StaticS16Ldg)
    }

    /// `"dynamic"` / `"static-s16"` — the cell-file storage variant.
    pub(crate) fn variant_name(self) -> &'static str {
        if self.is_static() {
            "static-s16"
        } else {
            "dynamic"
        }
    }

    /// `"LDG"` / `"LDC"` — the program residency.
    pub(crate) fn residency_name(self) -> &'static str {
        match self.residency() {
            InterpResidency::Ldg => "LDG",
            InterpResidency::Ldc => "LDC",
        }
    }

    /// Human-readable config label, e.g. `"static-s16/LDC"`.
    pub(crate) fn label(self) -> String {
        format!("{}/{}", self.variant_name(), self.residency_name())
    }

    pub(crate) fn threads_per_block(self) -> u32 {
        BENCH_INTERP_THREADS_PER_BLOCK
    }

    /// `true` when this config has no instantiated kernel (`StaticS16Ldg`).
    pub(crate) fn kernel_absent(self) -> bool {
        self.kernel().is_none()
    }

    /// The kernel symbol for this config, or `None` when the config is not
    /// instantiated (`StaticS16Ldg`).
    fn kernel(self) -> Option<unsafe extern "C" fn(InterpDesc3)> {
        match self {
            FwdVmConfig::DynamicLdg => Some(ab_gkr_bench_fwd_vm_ldg_kernel),
            FwdVmConfig::DynamicLdc => Some(ab_gkr_bench_fwd_vm_ldc_kernel),
            FwdVmConfig::StaticS16Ldc => Some(ab_gkr_bench_fwd_vm_ldc_s16_kernel),
            FwdVmConfig::StaticS16Ldg => None,
        }
    }
}

/// Per-block dynamic-smem the fwd-VM cell file needs: `budget` u32 lanes per
/// thread (Base cell = 1 lane, Ext = 4 lanes 4-aligned), interleaved
/// `smem[c * blockDim.x + t]` — matches the `.cu`'s
/// `extern __shared__ u32 fwd_vm_smem[]` sizing.
pub(crate) fn fwd_vm_dynamic_smem_bytes(budget: u32, threads_per_block: u32) -> usize {
    budget as usize * std::mem::size_of::<u32>() * threads_per_block as usize
}

/// Launch the fwd-VM interpreter kernel (row-per-thread) over `desc.count`
/// rows. For `InterpResidency::Ldc` the caller must already have uploaded
/// `setup.lanes` via `upload_bench_program_to_constant` (and may null
/// `desc.program_ldg`). Enqueues on `exec_stream`.
pub(crate) fn launch_fwd_vm(
    desc: &InterpDesc3,
    residency: InterpResidency,
    context: &ProverContext,
) -> CudaResult<()> {
    let tpb = BENCH_INTERP_THREADS_PER_BLOCK;
    let grid_dim = desc.count.max(1).div_ceil(tpb);
    let smem = fwd_vm_dynamic_smem_bytes(desc.budget, tpb);
    // Committed budgets are 16 cells (8 KB/block at 128 threads) — far below
    // the 48 KB default cap, so no large-smem opt-in path is needed here.
    assert!(
        smem <= BENCH_INTERP_DEFAULT_SMEM_CAP,
        "fwd-VM smem {smem} exceeds the default cap; add the opt-in before raising budgets"
    );
    let kernel = match residency {
        InterpResidency::Ldg => ab_gkr_bench_fwd_vm_ldg_kernel,
        InterpResidency::Ldc => ab_gkr_bench_fwd_vm_ldc_kernel,
    };
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(tpb)
        .dynamic_smem_bytes(smem)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrBenchFwdVmArguments::new(*desc);
    GkrBenchFwdVmFunction(kernel).launch(&config, &args)
}

/// Launch the fwd-VM interpreter for a specific A/B `config` (Task 7). The
/// dynamic variants request `budget * 4 * tpb` dynamic smem; the static variant
/// requests ZERO dynamic smem (its cell file is a compile-time `__shared__`
/// array), and requires `desc.budget == FWD_VM_STATIC_BUDGET`. Panics if called
/// for `StaticS16Ldg` (no kernel). LDC configs assume the caller already
/// uploaded `setup.lanes` via `upload_bench_program_to_constant`. Enqueues on
/// `exec_stream`.
pub(crate) fn launch_fwd_vm_config(
    desc: &InterpDesc3,
    config: FwdVmConfig,
    context: &ProverContext,
) -> CudaResult<()> {
    let kernel = config
        .kernel()
        .expect("launch_fwd_vm_config: StaticS16Ldg has no instantiated kernel");
    let tpb = config.threads_per_block();
    let grid_dim = desc.count.max(1).div_ceil(tpb);
    let smem = if config.is_static() {
        assert_eq!(
            desc.budget, FWD_VM_STATIC_BUDGET,
            "static-s16 kernel requires desc.budget == {FWD_VM_STATIC_BUDGET}, got {}",
            desc.budget
        );
        0
    } else {
        fwd_vm_dynamic_smem_bytes(desc.budget, tpb)
    };
    assert!(
        smem <= BENCH_INTERP_DEFAULT_SMEM_CAP,
        "fwd-VM smem {smem} exceeds the default cap; add the opt-in before raising budgets"
    );
    let launch_config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(tpb)
        .dynamic_smem_bytes(smem)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrBenchFwdVmArguments::new(*desc);
    GkrBenchFwdVmFunction(kernel).launch(&launch_config, &args)
}

/// Static blocks-per-SM the `config` achieves at `budget` (128 threads). For the
/// dynamic variants the query uses the `budget`-implied dynamic-smem footprint;
/// for the static variant the dynamic footprint is 0 (its compile-time
/// `__shared__` array is already accounted for by ptxas, so the occupancy API
/// reflects it automatically). Returns `None` for `StaticS16Ldg` (no kernel).
pub(crate) fn fwd_vm_blocks_per_sm(config: FwdVmConfig, budget: u32) -> CudaResult<Option<i32>> {
    let Some(kernel) = config.kernel() else {
        return Ok(None);
    };
    let tpb = config.threads_per_block();
    let smem = if config.is_static() {
        0
    } else {
        fwd_vm_dynamic_smem_bytes(budget, tpb)
    };
    let blocks = era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        &GkrBenchFwdVmFunction(kernel),
        tpb as i32,
        smem,
    )?;
    Ok(Some(blocks))
}

/// Write 0 into the device `error_flag` word (bench/test harness; synchronous).
fn reset_error_flag(ptr: *mut u32, context: &ProverContext) {
    let zero = [0u32];
    let stream = context.get_exec_stream();
    // SAFETY: `ptr` is `setup.desc.error_flag`, a resident 1-element device u32.
    let dst = unsafe { DeviceSlice::from_raw_parts_mut(ptr, 1) };
    memory_copy_async(dst, &zero, stream).unwrap();
    stream.synchronize().unwrap();
}

/// Read back the device `error_flag` word (bench/test harness; synchronous).
fn read_error_flag(ptr: *const u32, context: &ProverContext) -> u32 {
    let mut host = [0u32];
    let stream = context.get_exec_stream();
    // SAFETY: `ptr` is `setup.desc.error_flag`, a resident 1-element device u32.
    let src = unsafe { DeviceSlice::from_raw_parts(ptr, 1) };
    memory_copy_async(&mut host, src, stream).unwrap();
    stream.synchronize().unwrap();
    host[0]
}

/// Time the fwd-VM INTERPRETER side of one (circuit, layer) for `config`, over
/// `iters` CUDA-event-timed launches at `setup.desc.count` rows (the caller caps
/// `count` before calling). Mirrors `harness.rs::time_interp`: for an LDC config
/// the program upload to `__constant__` happens ONCE before the timed loop.
/// Returns `Some((median_ms, min_ms))`, or `None` when the config has no kernel
/// (`StaticS16Ldg`) or when an LDC program does not fit the constant array
/// (caller records a skip). PANICS if the kernel raised any `FWDVM_ERR_*` bit
/// (a broken kernel must not silently yield a timing number — the four gates
/// certify the dynamic variants, this guards the un-gated static variant).
pub(crate) fn time_fwd_vm(
    fixture: &CircuitFixture,
    setup: &FwdVmDeviceSetup,
    config: FwdVmConfig,
    iters: usize,
) -> Option<(f32, f32)> {
    config.kernel()?; // StaticS16Ldg: no kernel — skip.
    let context = fixture.context();
    let stream = context.get_exec_stream();

    if config.residency() == InterpResidency::Ldc {
        // ONE memcpyToSymbol before the timed loop; bail if the program is too
        // large for the constant array (never expected for the committed corpus).
        if !upload_bench_program_to_constant(&setup.lanes).unwrap() {
            return None;
        }
        stream.synchronize().unwrap();
    }

    reset_error_flag(setup.desc.error_flag, context);
    let desc = setup.desc;
    let (median, min) = super::harness::time_iters(stream, iters, || {
        launch_fwd_vm_config(&desc, config, context).unwrap();
    });
    let err = read_error_flag(setup.desc.error_flag as *const u32, context);
    assert_eq!(
        err, 0,
        "fwd-VM timing kernel raised error_flag = {err:#x} for config {} \
         (broken kernel — timing would be meaningless)",
        config.label()
    );
    Some((median, min))
}
