//! Backward coefficient-term ISA: descriptor ABI, lowering and launch.
//!
//! The launch geometry is §11's: ONE thread per logical row and
//! [`BWD_COEFF_ROWS_PER_BLOCK`] logical rows per block, with dynamic shared
//! memory sized exactly `cell_budget * size_of::<E4>() * threads_per_block` for
//! the per-thread private cell file. There is no two-half role split.
//!
//! The kernel is specialized by `(Regime, FoldDepth, CoeffBank)`; the cell
//! budget is runtime launch metadata, so one instantiation covers c2 through
//! c16. There is no ABI or runtime switch back to the retired generic backward
//! DAG VM: it is gone, not disabled.
//!
//! # Running the tests — `--features bench` is REQUIRED
//!
//! Everything below that carries the correctness story is
//! `#[cfg(all(test, feature = "bench"))]`: [`gpu_tests`] (the parity ladder, the
//! release-executor coverage gate, the sweep and the profiler), [`report`], and
//! [`compile`]'s fixture loader with its tests. A plain
//! `cargo test -p gpu_circuit_prover` compiles NONE of them and exits 0 having run
//! none of the four GPU gates. Only [`abi_tests`] — the Rust↔CUDA ABI gate — is
//! always compiled.
//!
//! Build unlocked, then run under the GPU lock:
//!
//! ```text
//! cargo test -p gpu_circuit_prover --release --features bench --no-run
//! .agents/bin/with_gpu_lock.sh <binary> --exact <test> --ignored --nocapture
//! ```
//!
//! `bwd_coeff_gating_notice` below states this in the default run's own output, and
//! `AB_REQUIRE_BENCH_GATES=1` turns a `bench`-less run into a failure for callers
//! that need non-vacuity proved rather than assumed.

pub(crate) mod compile;
pub(crate) mod desc;
#[cfg(all(test, feature = "bench"))]
mod gpu_tests;
pub(crate) mod lower;
#[cfg(all(test, feature = "bench"))]
mod report;
/// Launchers for the SEGMENTED lean VM: its own `__constant__` coefficient bank,
/// the `32 * k`-thread tile geometry, and the three epilogue specializations. The
/// cell-era launchers below are untouched — the two lineages share no symbol.
pub(crate) mod seg;
/// The segmented lean VM's fixture bridge: lean artifact plus round binding to
/// [`seg_lower::BwdSegSetup`], and the host storage model its CPU oracles resolve
/// through. `bench`-gated like [`compile`], and for the same reason.
#[cfg(all(test, feature = "bench"))]
mod seg_compile;
/// The SEGMENTED lean VM's launch descriptors (a separate lineage: it shares
/// only [`desc::BwdCoeffSourceWindow`] and the publication threshold with the
/// cell-era descriptor above).
pub(crate) mod seg_desc;
/// The segmented lean VM's GPU parity ladder: `K`, rounds, epilogues, D2 policies,
/// a nonzero `c_init` and the d3→d4 chain, each against BOTH CPU oracles and the
/// incumbent round update. `bench`-gated and `#[ignore]`d, like [`gpu_tests`].
#[cfg(all(test, feature = "bench"))]
mod seg_gpu_tests;
/// Host lowering for the segmented lean VM: per-round source classes, the
/// publish-scratch plan, and the validated by-value descriptor.
pub(crate) mod seg_lower;

#[cfg(test)]
mod abi_tests;
#[cfg(test)]
mod seg_abi_tests;
#[cfg(test)]
mod seg_lower_tests;

/// Makes the `bench`-feature gating above visible from a DEFAULT test run.
///
/// This plan has produced six vacuous-verification incidents, several of them the
/// same shape: a runner that matched nothing, exited 0, and read as a pass. The
/// whole coefficient-ISA GPU suite being feature-gated is a standing instance of
/// that shape — `cargo test -p gpu_circuit_prover` is green whether or not a single
/// gate ran.
///
/// So this module is deliberately NOT feature-gated. It does three things:
///
///   1. names the required invocation in the default run's own output, under a test
///      name that says what is missing;
///   2. under `--features bench`, references a marker the gated module defines, so
///      the suite is proved to have compiled rather than assumed; and
///   3. honours `AB_REQUIRE_BENCH_GATES=1` by FAILING a `bench`-less run — the
///      opt-in a CI job or an agent uses when "the GPU gates ran" is the claim
///      being made.
///
/// It does not fail a plain developer run: making the default invocation red would
/// just teach people to ignore it.
#[cfg(test)]
mod gating {
    /// The four gates §15's acceptance rests on, so a reader of a `bench`-less run
    /// can see exactly what did not execute.
    const GPU_GATES: [&str; 4] = [
        "bwd_coeff_source_resolution_smoke",
        "bwd_coeff_add_sub_l0_r0_spike",
        "bwd_coeff_add_sub_l0_d0_d3_parity",
        "bwd_coeff_release_executor_covers_every_form",
    ];

    const REQUIRE_ENV: &str = "AB_REQUIRE_BENCH_GATES";

    #[test]
    fn bwd_coeff_gating_notice() {
        let invocation = "cargo test -p gpu_circuit_prover --release --features bench --no-run, \
                          then run the binary under .agents/bin/with_gpu_lock.sh";

        #[cfg(feature = "bench")]
        {
            // A real link to the gated module: if `gpu_tests` is renamed, moved or
            // loses its marker, this stops compiling under `--features bench`
            // instead of silently going back to proving nothing.
            assert!(
                super::gpu_tests::GPU_PARITY_SUITE_COMPILED,
                "the bench-gated GPU parity suite must be compiled in a bench build"
            );
            eprintln!(
                "[bwd-coeff] bench feature ON: the GPU parity suite is compiled. \
                 Its four gates are #[ignore]d GPU tests -- {GPU_GATES:?} -- so they \
                 still need --ignored to actually run."
            );
        }

        #[cfg(not(feature = "bench"))]
        {
            let message = format!(
                "[bwd-coeff] bench feature OFF: the backward coefficient-ISA GPU suite \
                 was NOT compiled and NONE of its gates ran ({GPU_GATES:?}). This run \
                 says nothing about them. To run them: {invocation}. Set \
                 {REQUIRE_ENV}=1 to make this a failure."
            );
            eprintln!("{message}");
            assert!(
                std::env::var_os(REQUIRE_ENV).is_none(),
                "{REQUIRE_ENV} is set, but this binary was built WITHOUT --features bench, \
                 so the GPU gates cannot have run. {message}"
            );
        }

        // Referenced in both configurations so neither arm carries a dead binding.
        assert!(!invocation.is_empty() && GPU_GATES.len() == 4);
    }
}

use std::ffi::c_void;
use std::ptr::null_mut;
use std::sync::OnceLock;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};

use self::desc::{
    BwdCoeffDesc, BWD_COEFF_FOLD_FACTOR_CAP, BWD_COEFF_MAX_BUDGET_CELLS, BWD_COEFF_MAX_FOLD_DEPTH,
    BWD_COEFF_MIN_BUDGET_CELLS, BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_COEFF_ROWS_PER_BLOCK,
    BWD_COEFF_THREADS_PER_BLOCK,
};
use self::lower::BwdCoeffSetup;
use crate::primitives::field::E4;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::ProverContext;
use crate::upstream::BwdRegime;

cuda_struct_and_stub! {
    static ab_gkr_flat_coefficients: [E4; FLAT_CONST_MAX];
}
cuda_struct_and_stub! {
    static ab_gkr_bwd_coeff_fold_factors: [E4; BWD_COEFF_FOLD_FACTOR_CAP];
}

cuda_kernel_signature_arguments_and_function!(
    GkrBwdCoeffBuildFoldFactors,
    round_challenges: *const E4,
    target_depth: u32,
    fold_depth: u32,
    fold_factors: *mut E4,
);
cuda_kernel_declaration!(
    ab_gkr_bwd_coeff_build_fold_factors_kernel(
        round_challenges: *const E4,
        target_depth: u32,
        fold_depth: u32,
        fold_factors: *mut E4
    )
);

macro_rules! declare_bwd_coeff_kernel {
    ($signature:ident, $symbol:ident) => {
        cuda_kernel_signature_arguments_and_function!(
            pub(crate) $signature,
            desc: BwdCoeffDesc,
        );
        cuda_kernel_declaration!(pub(crate) $symbol(desc: BwdCoeffDesc));
    };
}

declare_bwd_coeff_kernel!(GkrBwdCoeffR0Const, ab_gkr_bwd_coeff_r0_const_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffR0Ptr, ab_gkr_bwd_coeff_r0_ptr_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD0Const, ab_gkr_bwd_coeff_ext_d0_const_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD0Ptr, ab_gkr_bwd_coeff_ext_d0_ptr_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD1Const, ab_gkr_bwd_coeff_ext_d1_const_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD1Ptr, ab_gkr_bwd_coeff_ext_d1_ptr_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD2Const, ab_gkr_bwd_coeff_ext_d2_const_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD2Ptr, ab_gkr_bwd_coeff_ext_d2_ptr_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD3Const, ab_gkr_bwd_coeff_ext_d3_const_kernel);
declare_bwd_coeff_kernel!(GkrBwdCoeffExtD3Ptr, ab_gkr_bwd_coeff_ext_d3_ptr_kernel);

/// §9.3's launch-wide coefficient storage choice. No term or value operand
/// carries an address-space tag, so this is a kernel specialization, never a
/// per-instruction decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)] // TASK 13 wires this into the main-layer prover.
pub(crate) enum BwdCoeffBank {
    /// The incumbent stream-ordered `__constant__` bank.
    Constant,
    /// The descriptor's single coefficient pointer. Used when a layer's bank
    /// exceeds the constant symbol — the corpus maximum is 1,138 recipes and
    /// the symbol holds [`FLAT_CONST_MAX`].
    DevicePointer,
}

impl BwdCoeffBank {
    /// Bank entries this storage can supply.
    pub(crate) const fn capacity(self) -> usize {
        match self {
            Self::Constant => FLAT_CONST_MAX,
            // A device buffer is bounded only by the thirteen-bit coefficient
            // index, minus the two reserved literals.
            Self::DevicePointer => {
                desc::BWD_COEFF_MAX_COEFFICIENT_ENCODINGS - desc::BWD_COEFF_INDEX_RESERVED as usize
            }
        }
    }
}

/// The bounded lazy-fold resolver this round needs (§10.2).
///
/// Rounds 0..=3 map to D0..D3. From round
/// [`BWD_COEFF_PUBLISH_TARGET_DEPTH`] + 1 on, every materializing source has
/// already published at its target depth, so a backing is at most ONE fold
/// behind and D1 is exact — which is why the resolver set stays bounded instead
/// of growing with the round index.
#[allow(dead_code)] // TASK 13 wires this into the main-layer prover.
pub(crate) fn bwd_coeff_fold_depth(round: u8) -> u8 {
    match round {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        _ => 1,
    }
}

fn fold_factor_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut ptr: *mut c_void = null_mut();
        // SAFETY: the Rust static is the stub for the exact CUDA
        // `__constant__` E4 factor bank.
        unsafe {
            cudaGetSymbolAddress(
                &mut ptr,
                &ab_gkr_bwd_coeff_fold_factors as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_bwd_coeff_fold_factors");
        ptr as usize
    });
    ptr as *mut E4
}

/// Derive this round's fold weights from the device-resident transcript
/// challenges. Enqueue-only, and skipped entirely at D0.
fn launch_fold_factor_prelude(setup: &BwdCoeffSetup, context: &ProverContext) -> CudaResult<()> {
    let desc = &setup.desc;
    if setup.fold_depth == 0 || desc.n_round_challenges == 0 || desc.round_challenges.is_null() {
        return Ok(());
    }
    let config = CudaLaunchConfig::basic(1, 32, context.get_exec_stream());
    let args = GkrBwdCoeffBuildFoldFactorsArguments::new(
        desc.round_challenges,
        desc.n_round_challenges,
        u32::from(setup.fold_depth),
        fold_factor_device_ptr(),
    );
    GkrBwdCoeffBuildFoldFactorsFunction(ab_gkr_bwd_coeff_build_fold_factors_kernel)
        .launch(&config, &args)
}

/// Dynamic shared memory for one block: the private E4 cell file of every
/// thread in it (§11).
#[allow(dead_code)] // TASK 13 wires this into the main-layer prover.
pub(crate) fn bwd_coeff_dynamic_smem_bytes(cell_budget: u32) -> usize {
    cell_budget as usize * core::mem::size_of::<E4>() * BWD_COEFF_THREADS_PER_BLOCK as usize
}

fn launch_config<'a>(desc: &BwdCoeffDesc, context: &'a ProverContext) -> CudaLaunchConfig<'a> {
    assert!(
        (BWD_COEFF_MIN_BUDGET_CELLS..=BWD_COEFF_MAX_BUDGET_CELLS).contains(&desc.cell_budget),
        "backward coefficient budget c{} is outside c{BWD_COEFF_MIN_BUDGET_CELLS}..c{BWD_COEFF_MAX_BUDGET_CELLS}",
        desc.cell_budget
    );
    CudaLaunchConfig::builder()
        .grid_dim(desc.logical_rows.max(1).div_ceil(BWD_COEFF_ROWS_PER_BLOCK))
        .block_dim(BWD_COEFF_THREADS_PER_BLOCK)
        .dynamic_smem_bytes(bwd_coeff_dynamic_smem_bytes(desc.cell_budget))
        .stream(context.get_exec_stream())
        .build()
}

/// Launch the exact `(Regime, FoldDepth, CoeffBank)` executor for this setup.
#[allow(dead_code)] // TASK 13 wires this into the main-layer prover.
pub(crate) fn launch_bwd_coeff(setup: &BwdCoeffSetup, context: &ProverContext) -> CudaResult<()> {
    launch_fold_factor_prelude(setup, context)?;
    let config = launch_config(&setup.desc, context);
    let desc = setup.desc;
    match (setup.regime, setup.fold_depth, setup.bank) {
        (BwdRegime::R0, _, BwdCoeffBank::Constant) => {
            GkrBwdCoeffR0ConstFunction(ab_gkr_bwd_coeff_r0_const_kernel)
                .launch(&config, &GkrBwdCoeffR0ConstArguments::new(desc))
        }
        (BwdRegime::R0, _, BwdCoeffBank::DevicePointer) => {
            GkrBwdCoeffR0PtrFunction(ab_gkr_bwd_coeff_r0_ptr_kernel)
                .launch(&config, &GkrBwdCoeffR0PtrArguments::new(desc))
        }
        (BwdRegime::Ext, 0, BwdCoeffBank::Constant) => {
            GkrBwdCoeffExtD0ConstFunction(ab_gkr_bwd_coeff_ext_d0_const_kernel)
                .launch(&config, &GkrBwdCoeffExtD0ConstArguments::new(desc))
        }
        (BwdRegime::Ext, 0, BwdCoeffBank::DevicePointer) => {
            GkrBwdCoeffExtD0PtrFunction(ab_gkr_bwd_coeff_ext_d0_ptr_kernel)
                .launch(&config, &GkrBwdCoeffExtD0PtrArguments::new(desc))
        }
        (BwdRegime::Ext, 1, BwdCoeffBank::Constant) => {
            GkrBwdCoeffExtD1ConstFunction(ab_gkr_bwd_coeff_ext_d1_const_kernel)
                .launch(&config, &GkrBwdCoeffExtD1ConstArguments::new(desc))
        }
        (BwdRegime::Ext, 1, BwdCoeffBank::DevicePointer) => {
            GkrBwdCoeffExtD1PtrFunction(ab_gkr_bwd_coeff_ext_d1_ptr_kernel)
                .launch(&config, &GkrBwdCoeffExtD1PtrArguments::new(desc))
        }
        (BwdRegime::Ext, 2, BwdCoeffBank::Constant) => {
            GkrBwdCoeffExtD2ConstFunction(ab_gkr_bwd_coeff_ext_d2_const_kernel)
                .launch(&config, &GkrBwdCoeffExtD2ConstArguments::new(desc))
        }
        (BwdRegime::Ext, 2, BwdCoeffBank::DevicePointer) => {
            GkrBwdCoeffExtD2PtrFunction(ab_gkr_bwd_coeff_ext_d2_ptr_kernel)
                .launch(&config, &GkrBwdCoeffExtD2PtrArguments::new(desc))
        }
        (BwdRegime::Ext, 3, BwdCoeffBank::Constant) => {
            GkrBwdCoeffExtD3ConstFunction(ab_gkr_bwd_coeff_ext_d3_const_kernel)
                .launch(&config, &GkrBwdCoeffExtD3ConstArguments::new(desc))
        }
        (BwdRegime::Ext, 3, BwdCoeffBank::DevicePointer) => {
            GkrBwdCoeffExtD3PtrFunction(ab_gkr_bwd_coeff_ext_d3_ptr_kernel)
                .launch(&config, &GkrBwdCoeffExtD3PtrArguments::new(desc))
        }
        (BwdRegime::Ext, depth, _) => panic!(
            "continuation fold depth D{depth} is outside D0..D{BWD_COEFF_MAX_FOLD_DEPTH}; \
             `bwd_coeff_fold_depth` is the only legal source of this value"
        ),
    }
}

/// Occupancy of the exact executor this setup would launch.
#[allow(dead_code)] // TASK 13 wires this into the main-layer prover.
pub(crate) fn bwd_coeff_blocks_per_sm(
    regime: BwdRegime,
    fold_depth: u8,
    bank: BwdCoeffBank,
    cell_budget: u32,
) -> CudaResult<i32> {
    assert!(
        (BWD_COEFF_MIN_BUDGET_CELLS..=BWD_COEFF_MAX_BUDGET_CELLS).contains(&cell_budget),
        "backward coefficient occupancy budget outside supported range"
    );
    let smem = bwd_coeff_dynamic_smem_bytes(cell_budget);
    let threads = BWD_COEFF_THREADS_PER_BLOCK as i32;
    macro_rules! occupancy {
        ($function:ident, $symbol:ident) => {
            era_cudart::occupancy::max_active_blocks_per_multiprocessor(
                &$function($symbol),
                threads,
                smem,
            )
        };
    }
    match (regime, fold_depth, bank) {
        (BwdRegime::R0, _, BwdCoeffBank::Constant) => {
            occupancy!(GkrBwdCoeffR0ConstFunction, ab_gkr_bwd_coeff_r0_const_kernel)
        }
        (BwdRegime::R0, _, BwdCoeffBank::DevicePointer) => {
            occupancy!(GkrBwdCoeffR0PtrFunction, ab_gkr_bwd_coeff_r0_ptr_kernel)
        }
        (BwdRegime::Ext, 0, BwdCoeffBank::Constant) => occupancy!(
            GkrBwdCoeffExtD0ConstFunction,
            ab_gkr_bwd_coeff_ext_d0_const_kernel
        ),
        (BwdRegime::Ext, 0, BwdCoeffBank::DevicePointer) => occupancy!(
            GkrBwdCoeffExtD0PtrFunction,
            ab_gkr_bwd_coeff_ext_d0_ptr_kernel
        ),
        (BwdRegime::Ext, 1, BwdCoeffBank::Constant) => occupancy!(
            GkrBwdCoeffExtD1ConstFunction,
            ab_gkr_bwd_coeff_ext_d1_const_kernel
        ),
        (BwdRegime::Ext, 1, BwdCoeffBank::DevicePointer) => occupancy!(
            GkrBwdCoeffExtD1PtrFunction,
            ab_gkr_bwd_coeff_ext_d1_ptr_kernel
        ),
        (BwdRegime::Ext, 2, BwdCoeffBank::Constant) => occupancy!(
            GkrBwdCoeffExtD2ConstFunction,
            ab_gkr_bwd_coeff_ext_d2_const_kernel
        ),
        (BwdRegime::Ext, 2, BwdCoeffBank::DevicePointer) => occupancy!(
            GkrBwdCoeffExtD2PtrFunction,
            ab_gkr_bwd_coeff_ext_d2_ptr_kernel
        ),
        (BwdRegime::Ext, 3, BwdCoeffBank::Constant) => occupancy!(
            GkrBwdCoeffExtD3ConstFunction,
            ab_gkr_bwd_coeff_ext_d3_const_kernel
        ),
        (BwdRegime::Ext, 3, BwdCoeffBank::DevicePointer) => occupancy!(
            GkrBwdCoeffExtD3PtrFunction,
            ab_gkr_bwd_coeff_ext_d3_ptr_kernel
        ),
        (BwdRegime::Ext, depth, _) => {
            panic!("continuation fold depth D{depth} is outside D0..D{BWD_COEFF_MAX_FOLD_DEPTH}")
        }
    }
}

const _: () = {
    // §10.2's publication threshold is what bounds the resolver set: past it a
    // backing is at most one fold behind.
    assert!(BWD_COEFF_MAX_FOLD_DEPTH == BWD_COEFF_PUBLISH_TARGET_DEPTH);
};
