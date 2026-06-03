//! End-to-end GPU parity harness for the vendored DIT NTT engine bring-up
//! kernels (`gpu/ntt/native/dit_kernels_extern.cu`).
//!
//! Covers all 12 single-pass configs:
//!   v8 (LOG_VPT=3): LOG_N ∈ {3,4,5,6,7,8}  → ab_dit_single_{3..8}_3
//!   v4 (LOG_VPT=2): LOG_N ∈ {2,3,4,5,6,7}  → ab_dit_single_{2..7}_2
//!
//! Every config is validated against red's `bitreversed_monomials_to_natural_evals`
//! oracle across ALL cosets emitted by a single grid=1 launch.
//!
//! Architecture notes (decided upstream — see the task spec):
//!  - The per-stage butterfly triangle (`tw_clean`) is computed in Rust and
//!    uploaded; there is NO host-side CUDA twiddle code in the bring-up path.
//!  - The engine reads the coset root ω on-device from red's Rust-initialized
//!    `ab_ntt_forward_powers` table (via `get_forward_twiddle_power`), so the
//!    harness MUST create a `DeviceContext` before launching (done by
//!    `make_context()`).

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

use fft::field_utils::domain_generator_for_size;
use serial_test::serial;

use super::make_context;
use crate::ntt_twiddles::OMEGA_LOG_ORDER;
use crate::upstream::{Field, PrimeField};
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut,
};
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

// ---------------------------------------------------------------------------
// Kernel bindings — one `cuda_kernel!` type shared by all single-pass symbols
// (they all have identical signatures), then one `dit_single!(sym)` per symbol.
// ---------------------------------------------------------------------------
cuda_kernel!(
    DitSingle,
    dit_single,
    monomials_bitrev: *const BF,
    tw_clean: *const BF,
    out_natural: *mut BF,
    cfp_0: u32,
    coset_step: u32,
    coset_out_stride: u32,
);

// v8 family (LOG_VPT=3), LOG_N 3..8
dit_single!(ab_dit_single_3_3);
dit_single!(ab_dit_single_4_3);
dit_single!(ab_dit_single_5_3);
dit_single!(ab_dit_single_6_3);
dit_single!(ab_dit_single_7_3);
dit_single!(ab_dit_single_8_3);
// v4 family (LOG_VPT=2), LOG_N 2..7
dit_single!(ab_dit_single_2_2);
dit_single!(ab_dit_single_3_2);
dit_single!(ab_dit_single_4_2);
dit_single!(ab_dit_single_5_2);
dit_single!(ab_dit_single_6_2);
dit_single!(ab_dit_single_7_2);

// ---------------------------------------------------------------------------
// Rust port of the deleted C++ host builder `build_clean_triangle<LOG_M,LOG_VPT>`
// (recovered from `git show d68a60a5^:gpu/ntt/native/dit_twiddles.cuh`).
// Ported index-for-index; only the host-arithmetic primitives differ (we use
// red's `BF` powering instead of the experiment's host Montgomery math).
// ---------------------------------------------------------------------------

/// `clean_triangle_count<LOG_M, LOG_VPT>()` == 2^M - 1.
const fn clean_triangle_count(log_m: u32, log_vpt: u32) -> usize {
    let lanes = 1usize << (log_m - log_vpt);
    (lanes << log_vpt) - 1
}

/// `hbr(x, n)` — bit-reverse of `x` within `n` bits (matches the C++ lambda).
fn hbr(x: u32, n: u32) -> u32 {
    let mut r = 0u32;
    for i in 0..n {
        r |= ((x >> i) & 1) << (n - 1 - i);
    }
    r
}

/// ω^idx, ω = order-2^27 root = `domain_generator_for_size::<BF>(1<<27)` (= 31^15),
/// the SAME root red's `ab_ntt_forward_powers` is built from. Matches the C++
/// `host_omega_pow(idx)`.
fn host_omega_pow(idx: u32) -> BF {
    let omega = domain_generator_for_size::<BF>(1u64 << OMEGA_LOG_ORDER);
    omega.pow(idx)
}

/// Port of `build_clean_triangle<LOG_M, LOG_VPT>(bf* dst)`. Fills `2^M - 1`
/// entries. CLEAN triangle: LANES rows keyed on `lane`, n2 absent, shift =
/// `27 - M`.
fn build_clean_triangle(log_m: u32, log_vpt: u32) -> Vec<BF> {
    let vpt: u32 = 1 << log_vpt;
    let lanes: u32 = 1 << (log_m - log_vpt);
    let shift: u32 = OMEGA_LOG_ORDER - log_m;

    // `off(s)` — stage-block offset within the per-thread triangle. For the
    // clean triangle LOG_TBL == LOG_M, so THREADS == LANES.
    let off = |s: u32| -> usize {
        let mut o = 0usize;
        for k in 0..s {
            o += if k < log_vpt {
                (lanes * (vpt >> (k + 1))) as usize
            } else {
                1usize << (log_m - 1 - k)
            };
        }
        o
    };

    let count = clean_triangle_count(log_m, log_vpt);
    let mut dst = vec![BF::ONE; count];
    for lane in 0..lanes {
        for s in 0..log_m {
            if s < log_vpt {
                let u = vpt >> (s + 1);
                for q in 0..u {
                    let grp = lane * u + q;
                    let entry = host_omega_pow(hbr(grp, log_m - 1) << shift);
                    dst[off(s) + (lane * u + q) as usize] = entry;
                }
            } else {
                let bg = lane >> (s + 1 - log_vpt);
                let entry = host_omega_pow(hbr(bg, log_m - 1) << shift);
                dst[off(s) + bg as usize] = entry;
            }
        }
    }
    dst
}

// ---------------------------------------------------------------------------
// Geometry helpers
// ---------------------------------------------------------------------------

/// Number of cosets emitted by a single grid=1 single-pass launch.
///
/// SLOTS_PER_BLOCK = NUM_WARPS * NTTS_PER_WARP = 4 * (32 / LANES)
/// where LANES = 1 << (log_n - log_vpt).
/// num_cosets = SLOTS_PER_BLOCK * K = 4 * (32 / LANES) * 8
///            = 1 << (10 - (log_n - log_vpt))
fn single_pass_num_cosets(log_n: u32, log_vpt: u32) -> usize {
    1usize << (10 - (log_n - log_vpt))
}

// ---------------------------------------------------------------------------
// Parameterized parity helper
// ---------------------------------------------------------------------------

/// Core single-pass parity check. Builds the triangle, runs the kernel on GPU,
/// and compares ALL emitted cosets against the oracle.
fn run_single_pass_parity(log_n: u32, log_vpt: u32) {
    let n: usize = 1 << log_n;
    let num_cosets = single_pass_num_cosets(log_n, log_vpt);
    // log_lde_factor satisfies num_cosets = 2^log_lde_factor.
    let log_lde_factor = num_cosets.trailing_zeros() as u32;
    assert_eq!(1usize << log_lde_factor, num_cosets);

    // coset_step = 2^(OMEGA_LOG_ORDER - log_n - log_lde_factor)
    let coset_step: u32 = 1 << (OMEGA_LOG_ORDER - log_n - log_lde_factor);
    let cfp_0: u32 = 0;

    let context = make_context();
    let stream = context.get_exec_stream();

    // Bit-reversed-order monomial coefficients shared by all cosets.
    let monomials_host: Vec<BF> = (0..n)
        .map(|idx| BF::new((17 + (idx as u32).wrapping_mul(31)) as u32))
        .collect();

    // --- Engine path ---------------------------------------------------------
    let tw_clean_host = build_clean_triangle(log_n, log_vpt);
    assert_eq!(tw_clean_host.len(), clean_triangle_count(log_n, log_vpt));
    assert_eq!(tw_clean_host.len(), n - 1);

    let mut monomials_dev = context.alloc(n).unwrap();
    let mut tw_clean_dev = context.alloc(tw_clean_host.len()).unwrap();
    let mut out_dev = context.alloc(num_cosets * n).unwrap();
    memory_copy_async(&mut monomials_dev, &monomials_host, stream).unwrap();
    memory_copy_async(&mut tw_clean_dev, &tw_clean_host, stream).unwrap();

    {
        let grid_dim: Dim3 = 1u32.into();
        let block_dim: Dim3 = (4u32 * 32u32).into(); // 128 threads = 4 warps
        let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        // All single-pass configs are < 48 KB — no cudaFuncSetAttribute needed.
        config.dynamic_smem_bytes =
            clean_triangle_count(log_n, log_vpt) * std::mem::size_of::<BF>();

        let mono_ptr = monomials_dev[..].as_ptr();
        let tw_ptr = tw_clean_dev[..].as_ptr();
        let out_ptr = (&mut out_dev[..]).as_mut_ptr();
        // coset_out_stride = N keeps the Phase-1 contiguous-output expectation.
        let coset_out_stride: u32 = 1u32 << log_n;
        let args = DitSingleArguments::new(
            mono_ptr,
            tw_ptr,
            out_ptr,
            cfp_0,
            coset_step,
            coset_out_stride,
        );

        // Dispatch to the correct kernel symbol for this (log_n, log_vpt).
        let result = match (log_n, log_vpt) {
            (3, 3) => DitSingleFunction(ab_dit_single_3_3).launch(&config, &args),
            (4, 3) => DitSingleFunction(ab_dit_single_4_3).launch(&config, &args),
            (5, 3) => DitSingleFunction(ab_dit_single_5_3).launch(&config, &args),
            (6, 3) => DitSingleFunction(ab_dit_single_6_3).launch(&config, &args),
            (7, 3) => DitSingleFunction(ab_dit_single_7_3).launch(&config, &args),
            (8, 3) => DitSingleFunction(ab_dit_single_8_3).launch(&config, &args),
            (2, 2) => DitSingleFunction(ab_dit_single_2_2).launch(&config, &args),
            (3, 2) => DitSingleFunction(ab_dit_single_3_2).launch(&config, &args),
            (4, 2) => DitSingleFunction(ab_dit_single_4_2).launch(&config, &args),
            (5, 2) => DitSingleFunction(ab_dit_single_5_2).launch(&config, &args),
            (6, 2) => DitSingleFunction(ab_dit_single_6_2).launch(&config, &args),
            (7, 2) => DitSingleFunction(ab_dit_single_7_2).launch(&config, &args),
            _ => panic!("unsupported single-pass config (log_n={log_n}, log_vpt={log_vpt})"),
        };
        result.unwrap();
    }

    let mut engine_host = vec![BF::ZERO; num_cosets * n];
    memory_copy_async(&mut engine_host, &out_dev, stream).unwrap();
    stream.synchronize().unwrap();

    // --- Reference (oracle) path ---------------------------------------------
    let mut monomials_ref_dev = context.alloc(n).unwrap();
    let mut ref_out_dev = context.alloc(n).unwrap();
    memory_copy_async(&mut monomials_ref_dev, &monomials_host, stream).unwrap();

    // Oracle: call the compact 1-pass kernel DIRECTLY (not via
    // `bitreversed_monomials_to_natural_evals`, which now routes the DIT range
    // to the engine under test — that would be circular). Compact reads twiddles
    // from `__constant__` tables, so it is a true independent baseline. All
    // single-pass configs have log_n <= 8 (<= 12), so 1-pass compact applies.
    let oracle_coset_factor_shift = OMEGA_LOG_ORDER - log_n - log_lde_factor;
    let device_props = context.get_device_properties();
    for cc in 0..num_cosets {
        {
            let inputs_matrix = DeviceMatrixChunk::new(&monomials_ref_dev[..], n, 0, n);
            let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut ref_out_dev[..], n, 0, n);
            // compact 1-pass only supports log_n in [4, 12]. For log_n <= 7 the
            // single-coset strategy entry is an independent baseline (it never
            // routes to DIT at num_cosets=1: no two-pass below log_n 8, and
            // single-pass needs num_cosets >> 1); log_n 8 uses 1-pass compact.
            if log_n <= 7 {
                super::super::ntt::bitreversed_monomials_to_natural_evals(
                    &inputs_matrix,
                    &mut outputs_matrix,
                    log_n as usize,
                    log_lde_factor as usize,
                    cc,
                    false,
                    context.device_context(),
                    None,
                    stream,
                    device_props,
                )
                .unwrap();
            } else {
                super::super::ntt::monomials_to_evals_compact_1_pass(
                    &inputs_matrix,
                    &mut outputs_matrix,
                    log_n as usize,
                    cc,
                    oracle_coset_factor_shift,
                    1,
                    1,
                    1,
                    false,
                    stream,
                )
                .unwrap();
            }
        }
        let mut ref_host = vec![BF::ZERO; n];
        memory_copy_async(&mut ref_host, &ref_out_dev, stream).unwrap();
        stream.synchronize().unwrap();

        let engine_coset = &engine_host[cc * n..cc * n + n];
        let mut first_mismatch = None;
        for k in 0..n {
            if engine_coset[k] != ref_host[k] {
                first_mismatch = Some(k);
                break;
            }
        }
        if let Some(first_k) = first_mismatch {
            // Dump first few mismatches before panicking.
            eprintln!(
                "DIT single-pass parity FAIL: log_n={log_n}, log_vpt={log_vpt}, \
                 coset={cc}/{num_cosets}"
            );
            for k in 0..n.min(8) {
                eprintln!(
                    "  k={k:3}  engine={:?}  expected={:?}{}",
                    engine_coset[k],
                    ref_host[k],
                    if engine_coset[k] != ref_host[k] {
                        "  <-- DIFF"
                    } else {
                        ""
                    }
                );
            }
            panic!(
                "DIT engine parity FAILED: log_n={log_n}, log_vpt={log_vpt}, \
                 coset={cc}, k={first_k}"
            );
        }
    }

    println!(
        "DIT single-pass parity PASS: log_n={log_n}, log_vpt={log_vpt}, \
         num_cosets={num_cosets} (all match red's oracle)"
    );
}

// ---------------------------------------------------------------------------
// Per-config test functions — clear failure attribution in the test runner.
// ---------------------------------------------------------------------------

macro_rules! dit_single_parity_test {
    ($name:ident, $log_n:expr, $log_vpt:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_single_pass_parity($log_n, $log_vpt);
        }
    };
}

// v8 family (LOG_VPT=3)
dit_single_parity_test!(dit_single_3_3_parity, 3, 3);
dit_single_parity_test!(dit_single_4_3_parity, 4, 3);
dit_single_parity_test!(dit_single_5_3_parity, 5, 3);
dit_single_parity_test!(dit_single_6_3_parity, 6, 3);
dit_single_parity_test!(dit_single_7_3_parity, 7, 3);
dit_single_parity_test!(dit_single_8_3_parity, 8, 3);
// v4 family (LOG_VPT=2)
dit_single_parity_test!(dit_single_2_2_parity, 2, 2);
dit_single_parity_test!(dit_single_3_2_parity, 3, 2);
dit_single_parity_test!(dit_single_4_2_parity, 4, 2); // was the original test
dit_single_parity_test!(dit_single_5_2_parity, 5, 2);
dit_single_parity_test!(dit_single_6_2_parity, 6, 2);
dit_single_parity_test!(dit_single_7_2_parity, 7, 2);

// ===========================================================================
// TWO-PASS family
//
// Covers all 10 two-pass configs:
//   v8 (LOG_VPT=3): LOG_N ∈ {9,10,11,12,13} → ab_dit_two_pass_{9..13}_3
//   v4 (LOG_VPT=2): LOG_N ∈ {8,9,10,11,12}  → ab_dit_two_pass_{8..12}_2
//
// Each config is exercised against red's `bitreversed_monomials_to_natural_evals`
// oracle across pow2-divisor grid shapes: grid=1 (one block does all cosets), a
// mid grid (grid = coset_count / 2), and grid = coset_count (one coset per
// block). The kernel processes EXACTLY `cosets_per_block = coset_count / grid`
// cosets per block, so `grid` MUST be a power-of-two divisor of the coset count
// (no ragged tail).
//
// Three new pieces relative to single-pass (all built host-side in Rust here):
//  - the pass-1 COUPLED triangle (`build_coupled_triangle`),
//  - the per-coset delta d-table (`build_coset_delta_table`),
//  - a larger-smem launch with the dynamic-smem opt-in (mirrors `ntt.rs`).
// The pass-2 CLEAN triangle reuses the proven `build_clean_triangle` (log_m =
// LOG_N2). The oracle mapping, ω, and coset twist are identical to single-pass.
// ===========================================================================

// One `cuda_kernel!` type shared by all two-pass symbols (identical signatures).
cuda_kernel!(
    DitTwoPass,
    dit_two_pass,
    monomials_bitrev: *const BF,
    tw_p1_coupled: *const BF,
    tw_p2_clean: *const BF,
    d_table: *const BF,
    out_natural: *mut BF,
    cfp_0: u32,
    coset_step: u32,
    cosets_per_block: u32,
    coset_out_stride: u32,
);

// v8 family (LOG_VPT=3), LOG_N 9..13
dit_two_pass!(ab_dit_two_pass_9_3);
dit_two_pass!(ab_dit_two_pass_10_3);
dit_two_pass!(ab_dit_two_pass_11_3);
dit_two_pass!(ab_dit_two_pass_12_3);
dit_two_pass!(ab_dit_two_pass_13_3);
// v4 family (LOG_VPT=2), LOG_N 8..12
dit_two_pass!(ab_dit_two_pass_8_2);
dit_two_pass!(ab_dit_two_pass_9_2);
dit_two_pass!(ab_dit_two_pass_10_2);
dit_two_pass!(ab_dit_two_pass_11_2);
dit_two_pass!(ab_dit_two_pass_12_2);

// ---------------------------------------------------------------------------
// Two-pass geometry (`NttTwoPassGeom`, from `gpu/ntt/native/dit_geometry.cuh`)
// replicated in Rust.
// ---------------------------------------------------------------------------
#[derive(Clone, Copy)]
struct TwoPassGeom {
    log_n: u32,
    log_vpt: u32,
    vpt: u32,
    n: u32,
    log_n1: u32,
    log_n2: u32,
    n1: u32,
    #[allow(dead_code)]
    n2: u32,
    threads: u32,
    #[allow(dead_code)]
    lanes_p1: u32,
    #[allow(dead_code)]
    lanes_p2: u32,
}

impl TwoPassGeom {
    fn new(log_n: u32, log_vpt: u32) -> Self {
        let vpt = 1u32 << log_vpt;
        let n = 1u32 << log_n;
        let log_n2 = (log_n / 2).min(log_vpt + 3);
        let log_n1 = log_n - log_n2;
        let n1 = 1u32 << log_n1;
        let n2 = 1u32 << log_n2;
        let threads = n / vpt;
        let lanes_p1 = 1u32 << (log_n1 - log_vpt);
        let lanes_p2 = 1u32 << (log_n2 - log_vpt);
        Self {
            log_n,
            log_vpt,
            vpt,
            n,
            log_n1,
            log_n2,
            n1,
            n2,
            threads,
            lanes_p1,
            lanes_p2,
        }
    }
}

/// `coupled_triangle_count<LOG_N, LOG_VPT, LOG_N1>()`
/// == THREADS*(VPT-1) + N2*(LANES_P1-1). Always a multiple of 4 (tail=0 for
/// `stage_triangle_v4`).
fn coupled_triangle_count(log_n: u32, log_vpt: u32, log_n1: u32) -> usize {
    let vpt = 1usize << log_vpt;
    let threads = 1usize << (log_n - log_vpt);
    let lanes_p1 = 1usize << (log_n1 - log_vpt);
    let n2 = 1usize << (log_n - log_n1);
    threads * (vpt - 1) + n2 * (lanes_p1 - 1)
}

// ---------------------------------------------------------------------------
// Rust port of `build_coupled_triangle<LOG_N, LOG_VPT, LOG_N1>(bf* dst)`
// (recovered from `git show d68a60a5^:gpu/ntt/native/dit_twiddles.cuh`).
// Ported index-for-index; only the host-arithmetic primitive differs (red `BF`
// powering via `host_omega_pow`). COUPLED triangle: THREADS rows keyed on tid,
// the n2-block folded into the group index; LOG_TBL = LOG_N, shift = 27 - N.
// ---------------------------------------------------------------------------
fn build_coupled_triangle(log_n: u32, log_vpt: u32, log_n1: u32) -> Vec<BF> {
    let vpt: u32 = 1 << log_vpt;
    let threads: u32 = 1 << (log_n - log_vpt);
    let lanes_p1: u32 = 1 << (log_n1 - log_vpt);
    let shift: u32 = OMEGA_LOG_ORDER - log_n;

    // `off(s)` — stage-block offset within the per-thread triangle. LOG_TBL ==
    // LOG_N here, so the local block scales with THREADS and the cross block is
    // 2^(LOG_N-1-s) (all n2 blocks' global groups).
    let off = |s: u32| -> usize {
        let mut o = 0usize;
        for k in 0..s {
            o += if k < log_vpt {
                (threads * (vpt >> (k + 1))) as usize
            } else {
                1usize << (log_n - 1 - k)
            };
        }
        o
    };

    let count = coupled_triangle_count(log_n, log_vpt, log_n1);
    let mut dst = vec![BF::ONE; count];
    for tid in 0..threads {
        let n2 = tid >> (log_n1 - log_vpt);
        let lane = tid & (lanes_p1 - 1);
        for s in 0..log_n1 {
            if s < log_vpt {
                let u = vpt >> (s + 1);
                for q in 0..u {
                    let grp = (n2 << (log_n1 - 1 - s)) | (lane * u + q);
                    let entry = host_omega_pow(hbr(grp, log_n - 1) << shift);
                    dst[off(s) + (tid * u + q) as usize] = entry;
                }
            } else {
                let bg = lane >> (s + 1 - log_vpt);
                let grp = (n2 << (log_n1 - 1 - s)) | bg;
                let entry = host_omega_pow(hbr(grp, log_n - 1) << shift);
                dst[off(s) + grp as usize] = entry;
            }
        }
    }
    dst
}

// ---------------------------------------------------------------------------
// Rust port of `build_coset_delta_table<LOG_N, LOG_VPT>(bf* dst, step_per_iter)`
// (from `/home/rr/code/ntt-experiments/include/twiddles_2pass.cuh`). Fills
// VPT*THREADS = N entries in natural index order:
//   d[i] = ω^(bitrev(i, LOG_N) * step_per_iter),  i ∈ [0, N).
// NO OMEGA_SHIFT — matches the kernel's `pow_omega` (br * step) convention.
// ---------------------------------------------------------------------------
fn build_coset_delta_table(log_n: u32, _log_vpt: u32, step_per_iter: u32) -> Vec<BF> {
    let n = 1usize << log_n;
    let mut dst = vec![BF::ONE; n];
    for (i, slot) in dst.iter_mut().enumerate() {
        let br = hbr(i as u32, log_n);
        *slot = host_omega_pow(br.wrapping_mul(step_per_iter));
    }
    dst
}

/// `ntt_two_pass_smem<LOG_N, LOG_VPT>()` in bytes:
/// `(coupled_count + P2C_PAD + N + N) * sizeof(BF)`, where
/// `P2C_PAD = (clean_count(LOG_N2, LOG_VPT) + 3) & !3`.
fn ntt_two_pass_smem_bytes(g: &TwoPassGeom) -> usize {
    let p1c = coupled_triangle_count(g.log_n, g.log_vpt, g.log_n1);
    let p2c = clean_triangle_count(g.log_n2, g.log_vpt);
    let p2c_pad = (p2c + 3) & !3;
    let w = p1c + p2c_pad + (g.n as usize) + (g.n as usize);
    w * std::mem::size_of::<BF>()
}

// ---------------------------------------------------------------------------
// Parameterized two-pass parity helper.
//
// Coset walk (must stay LDE-compatible so red's oracle applies):
//   block `bx` processes EXACTLY `cosets_per_block` cosets
//   {bx, bx+grid, bx+2·grid, …, bx+(cosets_per_block-1)·grid}; iteration `c`
//   writes coset `ci = bx + c·grid` to out[ci*N .. ci*N+N], with twist exponent
//   cfp = cfp_0 + ci·coset_step.
// `grid` MUST be a power-of-two divisor of `total` so `grid * cosets_per_block
// == total` exactly and the grid-walk covers every coset with no ragged tail
// (the kernel no longer supports `grid ∤ total`). With cfp_0=0 and
// coset_step=2^(27 - LOG_N - log_lde_factor), global coset `ci` maps to red
// coset index `ci` (identical to the single-pass harness). The d-table is built
// with step_per_iter = grid * coset_step.
// ---------------------------------------------------------------------------
fn run_two_pass_parity(log_n: u32, log_vpt: u32, total: u32, grid: u32) {
    let g = TwoPassGeom::new(log_n, log_vpt);
    let n: usize = g.n as usize;

    // log_lde_factor satisfies total = 2^log_lde_factor.
    assert!(total.is_power_of_two(), "total must be a power of two");
    let log_lde_factor = total.trailing_zeros();
    assert!(
        log_n + log_lde_factor <= OMEGA_LOG_ORDER,
        "log_n + log_lde_factor must be <= {OMEGA_LOG_ORDER}"
    );

    // `grid` is FREE: the streaming kernel grid-strides cosets `bx, bx+gd, … <
    // total` with the loop condition as the guard (no divisibility, no ragged
    // tail). Any `grid` in `[1, total]` — including non-divisors — is valid.
    assert!(grid >= 1, "grid must be >= 1");

    let coset_step: u32 = 1 << (OMEGA_LOG_ORDER - log_n - log_lde_factor);
    let cfp_0: u32 = 0;
    let step_per_iter: u32 = grid.wrapping_mul(coset_step);

    let context = make_context();
    let stream = context.get_exec_stream();

    // Bit-reversed-order monomial coefficients shared by all cosets.
    let monomials_host: Vec<BF> = (0..n)
        .map(|idx| BF::new((17 + (idx as u32).wrapping_mul(31)) as u32))
        .collect();

    // --- Engine path ---------------------------------------------------------
    let tw_p1_host = build_coupled_triangle(log_n, log_vpt, g.log_n1);
    assert_eq!(
        tw_p1_host.len(),
        coupled_triangle_count(log_n, log_vpt, g.log_n1)
    );
    let tw_p2_host = build_clean_triangle(g.log_n2, log_vpt);
    assert_eq!(tw_p2_host.len(), clean_triangle_count(g.log_n2, log_vpt));
    assert_eq!(tw_p2_host.len(), (1usize << g.log_n2) - 1);
    let d_table_host = build_coset_delta_table(log_n, log_vpt, step_per_iter);
    assert_eq!(d_table_host.len(), n);

    let mut monomials_dev = context.alloc(n).unwrap();
    let mut tw_p1_dev = context.alloc(tw_p1_host.len()).unwrap();
    let mut tw_p2_dev = context.alloc(tw_p2_host.len()).unwrap();
    let mut d_table_dev = context.alloc(d_table_host.len()).unwrap();
    let mut out_dev = context.alloc((total as usize) * n).unwrap();
    memory_copy_async(&mut monomials_dev, &monomials_host, stream).unwrap();
    memory_copy_async(&mut tw_p1_dev, &tw_p1_host, stream).unwrap();
    memory_copy_async(&mut tw_p2_dev, &tw_p2_host, stream).unwrap();
    memory_copy_async(&mut d_table_dev, &d_table_host, stream).unwrap();

    let smem_bytes = ntt_two_pass_smem_bytes(&g);

    {
        let grid_dim: Dim3 = grid.into();
        let block_dim: Dim3 = g.threads.into();
        let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        config.dynamic_smem_bytes = smem_bytes;

        let mono_ptr = monomials_dev[..].as_ptr();
        let tw_p1_ptr = tw_p1_dev[..].as_ptr();
        let tw_p2_ptr = tw_p2_dev[..].as_ptr();
        let d_ptr = d_table_dev[..].as_ptr();
        let out_ptr = (&mut out_dev[..]).as_mut_ptr();
        // coset_out_stride = N keeps the Phase-1 contiguous-output expectation.
        let coset_out_stride: u32 = 1u32 << log_n;
        let args = DitTwoPassArguments::new(
            mono_ptr,
            tw_p1_ptr,
            tw_p2_ptr,
            d_ptr,
            out_ptr,
            cfp_0,
            coset_step,
            total,
            coset_out_stride,
        );

        // Resolve the kernel symbol for this (log_n, log_vpt).
        let function = match (log_n, log_vpt) {
            (9, 3) => DitTwoPassFunction(ab_dit_two_pass_9_3),
            (10, 3) => DitTwoPassFunction(ab_dit_two_pass_10_3),
            (11, 3) => DitTwoPassFunction(ab_dit_two_pass_11_3),
            (12, 3) => DitTwoPassFunction(ab_dit_two_pass_12_3),
            (13, 3) => DitTwoPassFunction(ab_dit_two_pass_13_3),
            (8, 2) => DitTwoPassFunction(ab_dit_two_pass_8_2),
            (9, 2) => DitTwoPassFunction(ab_dit_two_pass_9_2),
            (10, 2) => DitTwoPassFunction(ab_dit_two_pass_10_2),
            (11, 2) => DitTwoPassFunction(ab_dit_two_pass_11_2),
            (12, 2) => DitTwoPassFunction(ab_dit_two_pass_12_2),
            _ => panic!("unsupported two-pass config (log_n={log_n}, log_vpt={log_vpt})"),
        };

        // Dynamic-smem opt-in (mirrors `ntt.rs`): large configs (LOG_N 12,13)
        // exceed the 48 KB default cap, so the MaxDynamicSharedMemorySize
        // attribute must be raised. Applied unconditionally to keep the launch
        // path uniform; it is a no-op below the cap.
        let func_ptr = function.as_ptr();
        unsafe {
            cudaFuncSetAttribute(
                func_ptr,
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                smem_bytes as i32,
            )
            .wrap()
            .unwrap();
        }
        function.launch(&config, &args).unwrap();
    }

    let mut engine_host = vec![BF::ZERO; (total as usize) * n];
    memory_copy_async(&mut engine_host, &out_dev, stream).unwrap();
    stream.synchronize().unwrap();

    // --- Reference (oracle) path ---------------------------------------------
    let mut monomials_ref_dev = context.alloc(n).unwrap();
    let mut ref_out_dev = context.alloc(n).unwrap();
    memory_copy_async(&mut monomials_ref_dev, &monomials_host, stream).unwrap();

    // Oracle: call the compact path DIRECTLY (not via
    // `bitreversed_monomials_to_natural_evals`, which now routes the DIT range
    // to the engine under test — that would be circular). Compact reads twiddles
    // from `__constant__` tables, so it is a true independent baseline. The
    // two-pass DIT range is log_n in [8, 13]: log_n <= 12 → 1-pass compact;
    // log_n == 13 → 2-pass-compact-initial.
    let oracle_coset_factor_shift = OMEGA_LOG_ORDER - log_n - log_lde_factor;
    for ci in 0..total as usize {
        {
            let inputs_matrix = DeviceMatrixChunk::new(&monomials_ref_dev[..], n, 0, n);
            let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut ref_out_dev[..], n, 0, n);
            if log_n <= 12 {
                super::super::ntt::monomials_to_evals_compact_1_pass(
                    &inputs_matrix,
                    &mut outputs_matrix,
                    log_n as usize,
                    ci,
                    oracle_coset_factor_shift,
                    1,
                    1,
                    1,
                    false,
                    stream,
                )
                .unwrap();
            } else {
                super::super::ntt::monomials_to_evals_2_pass_compact_initial(
                    &inputs_matrix,
                    &mut outputs_matrix,
                    log_n as usize,
                    ci,
                    oracle_coset_factor_shift,
                    1,
                    1,
                    1,
                    1,
                    false,
                    stream,
                )
                .unwrap();
            }
        }
        let mut ref_host = vec![BF::ZERO; n];
        memory_copy_async(&mut ref_host, &ref_out_dev, stream).unwrap();
        stream.synchronize().unwrap();

        let engine_coset = &engine_host[ci * n..ci * n + n];
        let mut first_mismatch = None;
        for k in 0..n {
            if engine_coset[k] != ref_host[k] {
                first_mismatch = Some(k);
                break;
            }
        }
        if let Some(first_k) = first_mismatch {
            eprintln!(
                "DIT two-pass parity FAIL: log_n={log_n}, log_vpt={log_vpt}, \
                 total={total}, grid={grid}, coset={ci}"
            );
            let mut dumped = 0;
            for k in 0..n {
                if engine_coset[k] != ref_host[k] {
                    eprintln!(
                        "  (coset={ci}, index={k}, got={:?}, expected={:?})",
                        engine_coset[k], ref_host[k]
                    );
                    dumped += 1;
                    if dumped >= 8 {
                        break;
                    }
                }
            }
            panic!(
                "DIT two-pass parity FAILED: log_n={log_n}, log_vpt={log_vpt}, \
                 total={total}, grid={grid}, coset={ci}, first_k={first_k}"
            );
        }
    }

    println!(
        "DIT two-pass parity PASS: log_n={log_n}, log_vpt={log_vpt}, \
         total={total}, grid={grid} (all cosets match red's oracle)"
    );
}

// ---------------------------------------------------------------------------
// Per-config two-pass tests. The kernel processes EXACTLY
// `cosets_per_block = total / grid` cosets per block, so `grid` must be a
// power-of-two divisor of `total` (no ragged tail). Each config covers a
// trivial single-coset case plus three pow2-divisor grids over a pow2 coset
// count (total=8):
//   - single coset:    total=1,  grid=1   (log_lde=0)
//   - grid=1:          total=8,  grid=1   (one block does all 8 cosets)
//   - mid grid:        total=8,  grid=4   (cosets_per_block = total/2 = 2)
//   - grid=total:      total=8,  grid=8   (one coset per block)
// All cases require log_n + log_lde_factor <= 27.
// ---------------------------------------------------------------------------
macro_rules! dit_two_pass_parity_test {
    ($name:ident, $log_n:expr, $log_vpt:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            // single coset
            run_two_pass_parity($log_n, $log_vpt, 1, 1);
            // grid = 1: one block does all cosets
            run_two_pass_parity($log_n, $log_vpt, 8, 1);
            // mid grid: cosets_per_block = coset_count / 2
            run_two_pass_parity($log_n, $log_vpt, 8, 4);
            // grid = coset_count: one coset per block
            run_two_pass_parity($log_n, $log_vpt, 8, 8);
            // ragged: grid does NOT divide total — exercises the streaming
            // guard (blocks do unequal trip counts; the loop condition is the
            // only bound). 5 blocks over 8 cosets: bx<3 do 2, bx>=3 do 1.
            run_two_pass_parity($log_n, $log_vpt, 8, 5);
        }
    };
}

// v8 family (LOG_VPT=3), LOG_N 9..13
dit_two_pass_parity_test!(dit_two_pass_9_3_parity, 9, 3);
dit_two_pass_parity_test!(dit_two_pass_10_3_parity, 10, 3);
dit_two_pass_parity_test!(dit_two_pass_11_3_parity, 11, 3);
dit_two_pass_parity_test!(dit_two_pass_12_3_parity, 12, 3);
dit_two_pass_parity_test!(dit_two_pass_13_3_parity, 13, 3);
// v4 family (LOG_VPT=2), LOG_N 8..12
dit_two_pass_parity_test!(dit_two_pass_8_2_parity, 8, 2);
dit_two_pass_parity_test!(dit_two_pass_9_2_parity, 9, 2);
dit_two_pass_parity_test!(dit_two_pass_10_2_parity, 10, 2);
dit_two_pass_parity_test!(dit_two_pass_11_2_parity, 11, 2);
dit_two_pass_parity_test!(dit_two_pass_12_2_parity, 12, 2);

// ===========================================================================
// PHASE-2 device twiddle FILL kernels — parity vs the Rust builders.
//
// The fill kernels (`gpu/ntt/native/dit_twiddle_fill.cu`, bound in
// `super::super::dit`) construct the per-config butterfly-triangle and coset
// d-table buffers ON-DEVICE, reading red's `ab_ntt_forward_powers` via
// `get_forward_twiddle_power`. They must reproduce the exact buffers the
// parity-proven Rust `build_clean_triangle` / `build_coupled_triangle` /
// `build_coset_delta_table` produce.
//
// Each test launches one fill kernel into a fresh device buffer (grid = 1, per
// the kernel's launch contract — the init-to-ONE handoff uses block-scoped
// `__syncthreads()`), copies it back, and asserts element-for-element equality
// vs the Rust builder. `make_context()` initializes `ab_ntt_forward_powers`
// (required before any fill launch).
// ===========================================================================

// These helpers launch through the production `fill_*` dispatchers in
// `crate::ntt::dit`, so they double as the regression guard for that crate's
// grid=1/block=256 launch contract and per-config dispatch.
use crate::ntt::dit::{fill_clean_triangle, fill_coupled_triangle, fill_d_table};

/// CLEAN-triangle fill parity for one `(log_m, log_vpt)`.
fn run_fill_clean_parity(log_m: u32, log_vpt: u32) {
    let ctx = make_context(); // initializes ab_ntt_forward_powers
    let stream = ctx.get_exec_stream();
    let expected = build_clean_triangle(log_m, log_vpt); // parity-proven Rust
    assert_eq!(
        expected.len(),
        crate::ntt::dit::clean_triangle_count(log_m, log_vpt)
    );

    let mut dev = ctx.alloc(expected.len()).unwrap();
    // Launch through the production dispatcher so this parity test guards the
    // grid=1/block=256 launch contract that lives in `dit.rs`.
    fill_clean_triangle(log_m, log_vpt, &mut dev[..], stream).unwrap();

    let mut got = vec![BF::ZERO; expected.len()];
    memory_copy_async(&mut got, &dev, stream).unwrap();
    stream.synchronize().unwrap();

    assert_eq!(
        got, expected,
        "clean fill kernel != Rust builder for log_m={log_m} log_vpt={log_vpt}"
    );
    println!(
        "DIT clean fill parity PASS: log_m={log_m}, log_vpt={log_vpt} ({} entries)",
        expected.len()
    );
}

/// COUPLED-triangle fill parity for one two-pass `(log_n, log_vpt)`.
fn run_fill_coupled_parity(log_n: u32, log_vpt: u32) {
    let ctx = make_context();
    let stream = ctx.get_exec_stream();
    let g = TwoPassGeom::new(log_n, log_vpt);
    let expected = build_coupled_triangle(log_n, log_vpt, g.log_n1);
    assert_eq!(
        expected.len(),
        crate::ntt::dit::coupled_triangle_count(log_n, log_vpt)
    );

    let mut dev = ctx.alloc(expected.len()).unwrap();
    // Launch through the production dispatcher (grid=1/block=256 contract in
    // `dit.rs`).
    fill_coupled_triangle(log_n, log_vpt, &mut dev[..], stream).unwrap();

    let mut got = vec![BF::ZERO; expected.len()];
    memory_copy_async(&mut got, &dev, stream).unwrap();
    stream.synchronize().unwrap();

    assert_eq!(
        got, expected,
        "coupled fill kernel != Rust builder for log_n={log_n} log_vpt={log_vpt} (log_n1={})",
        g.log_n1
    );
    println!(
        "DIT coupled fill parity PASS: log_n={log_n}, log_vpt={log_vpt}, log_n1={} ({} entries)",
        g.log_n1,
        expected.len()
    );
}

/// D-TABLE fill parity for one two-pass `log_n`, exercising a representative
/// non-trivial `step_per_iter`. A real two-pass d-table uses
/// `step_per_iter = grid * coset_step` with `coset_step = 2^(27 - log_n - log_lde)`;
/// we sample `log_lde = 1, grid = 4` (the harness's divisible-multi shape).
fn run_fill_d_table_parity(log_n: u32) {
    let ctx = make_context();
    let stream = ctx.get_exec_stream();

    let log_lde = 1u32;
    let grid = 4u32;
    let coset_step: u32 = 1 << (OMEGA_LOG_ORDER - log_n - log_lde);
    let step_per_iter: u32 = grid.wrapping_mul(coset_step);

    let expected = build_coset_delta_table(log_n, 0, step_per_iter);
    assert_eq!(expected.len(), 1usize << log_n);

    let mut dev = ctx.alloc(expected.len()).unwrap();
    // Launch through the production dispatcher (grid=1/block=256 contract in
    // `dit.rs`).
    fill_d_table(log_n, &mut dev[..], step_per_iter, stream).unwrap();

    let mut got = vec![BF::ZERO; expected.len()];
    memory_copy_async(&mut got, &dev, stream).unwrap();
    stream.synchronize().unwrap();

    assert_eq!(
        got, expected,
        "d-table fill kernel != Rust builder for log_n={log_n} step_per_iter={step_per_iter}"
    );
    println!(
        "DIT d-table fill parity PASS: log_n={log_n}, step_per_iter={step_per_iter} ({} entries)",
        expected.len()
    );
}

macro_rules! dit_fill_clean_parity_test {
    ($name:ident, $log_m:expr, $log_vpt:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_fill_clean_parity($log_m, $log_vpt);
        }
    };
}

macro_rules! dit_fill_coupled_parity_test {
    ($name:ident, $log_n:expr, $log_vpt:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_fill_coupled_parity($log_n, $log_vpt);
        }
    };
}

macro_rules! dit_fill_d_table_parity_test {
    ($name:ident, $log_n:expr) => {
        #[test]
        #[cfg(not(no_cuda))]
        #[serial]
        fn $name() {
            run_fill_d_table_parity($log_n);
        }
    };
}

// CLEAN: the deduped 12-pair set.
dit_fill_clean_parity_test!(dit_fill_clean_2_2_parity, 2, 2);
dit_fill_clean_parity_test!(dit_fill_clean_3_2_parity, 3, 2);
dit_fill_clean_parity_test!(dit_fill_clean_3_3_parity, 3, 3);
dit_fill_clean_parity_test!(dit_fill_clean_4_2_parity, 4, 2);
dit_fill_clean_parity_test!(dit_fill_clean_4_3_parity, 4, 3);
dit_fill_clean_parity_test!(dit_fill_clean_5_2_parity, 5, 2);
dit_fill_clean_parity_test!(dit_fill_clean_5_3_parity, 5, 3);
dit_fill_clean_parity_test!(dit_fill_clean_6_2_parity, 6, 2);
dit_fill_clean_parity_test!(dit_fill_clean_6_3_parity, 6, 3);
dit_fill_clean_parity_test!(dit_fill_clean_7_2_parity, 7, 2);
dit_fill_clean_parity_test!(dit_fill_clean_7_3_parity, 7, 3);
dit_fill_clean_parity_test!(dit_fill_clean_8_3_parity, 8, 3);

// COUPLED: every two-pass config.
dit_fill_coupled_parity_test!(dit_fill_coupled_9_3_parity, 9, 3);
dit_fill_coupled_parity_test!(dit_fill_coupled_10_3_parity, 10, 3);
dit_fill_coupled_parity_test!(dit_fill_coupled_11_3_parity, 11, 3);
dit_fill_coupled_parity_test!(dit_fill_coupled_12_3_parity, 12, 3);
dit_fill_coupled_parity_test!(dit_fill_coupled_13_3_parity, 13, 3);
dit_fill_coupled_parity_test!(dit_fill_coupled_8_2_parity, 8, 2);
dit_fill_coupled_parity_test!(dit_fill_coupled_9_2_parity, 9, 2);
dit_fill_coupled_parity_test!(dit_fill_coupled_10_2_parity, 10, 2);
dit_fill_coupled_parity_test!(dit_fill_coupled_11_2_parity, 11, 2);
dit_fill_coupled_parity_test!(dit_fill_coupled_12_2_parity, 12, 2);

// D-TABLE: every two-pass LOG_N.
dit_fill_d_table_parity_test!(dit_fill_d_table_8_parity, 8);
dit_fill_d_table_parity_test!(dit_fill_d_table_9_parity, 9);
dit_fill_d_table_parity_test!(dit_fill_d_table_10_parity, 10);
dit_fill_d_table_parity_test!(dit_fill_d_table_11_parity, 11);
dit_fill_d_table_parity_test!(dit_fill_d_table_12_parity, 12);
dit_fill_d_table_parity_test!(dit_fill_d_table_13_parity, 13);

// ===========================================================================
// PHASE-2 Task 2 — context-init triangle precompute parity.
//
// `DeviceContext::create` builds the FULL fixed triangle set on-device (the
// CLEAN + COUPLED config arrays in `super::super::dit`) right after the ω table
// is uploaded. This test copies each precomputed buffer back and asserts it
// equals the parity-proven Rust builder for that config — confirming the
// init-time fill produced the right tables for the whole set.
// ===========================================================================
#[test]
#[cfg(not(no_cuda))]
#[serial]
fn dit_context_triangle_precompute_parity() {
    use super::super::dit::{CLEAN_CONFIGS, COUPLED_CONFIGS};
    use crate::ntt_twiddles::DeviceContext;
    use era_cudart::memory::memory_copy;

    // log_n=13 covers every coupled config (max two-pass LOG_N).
    let ctx = DeviceContext::create(13).unwrap();

    for &(log_m, log_vpt) in CLEAN_CONFIGS {
        let (log_m, log_vpt) = (log_m as u32, log_vpt as u32);
        let expected = build_clean_triangle(log_m, log_vpt);
        let dev = ctx.clean_triangle(log_m, log_vpt);
        assert_eq!(
            dev.len(),
            expected.len(),
            "clean triangle len mismatch for log_m={log_m} log_vpt={log_vpt}"
        );
        let mut got = vec![BF::ZERO; expected.len()];
        memory_copy(&mut got, dev).unwrap();
        assert_eq!(
            got, expected,
            "precomputed clean triangle != Rust builder for log_m={log_m} log_vpt={log_vpt}"
        );
        println!(
            "DIT context clean triangle PASS: log_m={log_m}, log_vpt={log_vpt} ({} entries)",
            expected.len()
        );
    }

    for &(log_n, log_vpt) in COUPLED_CONFIGS {
        let (log_n, log_vpt) = (log_n as u32, log_vpt as u32);
        let g = TwoPassGeom::new(log_n, log_vpt);
        let expected = build_coupled_triangle(log_n, log_vpt, g.log_n1);
        let dev = ctx.coupled_triangle(log_n, log_vpt);
        assert_eq!(
            dev.len(),
            expected.len(),
            "coupled triangle len mismatch for log_n={log_n} log_vpt={log_vpt}"
        );
        let mut got = vec![BF::ZERO; expected.len()];
        memory_copy(&mut got, dev).unwrap();
        assert_eq!(
            got, expected,
            "precomputed coupled triangle != Rust builder for log_n={log_n} log_vpt={log_vpt} \
             (log_n1={})",
            g.log_n1
        );
        println!(
            "DIT context coupled triangle PASS: log_n={log_n}, log_vpt={log_vpt}, log_n1={} \
             ({} entries)",
            g.log_n1,
            expected.len()
        );
    }
}

// ===========================================================================
// PHASE-2 Task 3 — production launcher (`monomials_to_evals_dit`) parity.
//
// Exercises the launcher end-to-end vs red's `bitreversed_monomials_to_natural_evals`
// oracle across BOTH paths (single-pass, two-pass) AND the strided/multi-column
// output layout enabled by the `coset_out_stride` ABI change. The launcher
// borrows the precomputed triangles from the `DeviceContext` and fills the
// two-pass d-table at runtime, so this covers the full production code path
// (minus strategy/dispatch wiring, which is Task 4).
//
// Output layout (column-major): coset `k`, column `col` occupies the matrix
// column `k*num_cols_per_coset + col`, i.e. BF offset
// `(k*num_cols_per_coset + col) * N`. With `num_cols_per_coset == num_ntts`
// the per-coset column blocks are back-to-back (strided > N), exercising the
// new per-coset output stride.
// ===========================================================================

/// Core launcher parity check. Builds `num_ntts` distinct monomial columns,
/// runs `monomials_to_evals_dit` into a strided output, and compares each
/// (coset, column) slab against red's per-coset oracle for that column.
fn run_launcher_parity(log_n: u32, log_vpt: u32, num_cosets: usize, num_ntts: usize) {
    use crate::ntt::dit::monomials_to_evals_dit;

    let n: usize = 1 << log_n;
    let num_cols_per_coset = num_ntts; // back-to-back strided (stride > N)
    let out_cols = num_cosets * num_cols_per_coset;

    // num_cosets = 2^log_lde_factor; coset_factor_shift = 27 - log_n - log_lde.
    assert!(num_cosets.is_power_of_two());
    let log_lde_factor = num_cosets.trailing_zeros();
    assert!(
        log_n + log_lde_factor <= OMEGA_LOG_ORDER,
        "log_n + log_lde_factor must be <= {OMEGA_LOG_ORDER}"
    );
    let coset_factor_shift: u32 = OMEGA_LOG_ORDER - log_n - log_lde_factor;
    let coset_index_base: usize = 0;

    let context = make_context();
    let stream = context.get_exec_stream();
    let device_props = context.get_device_properties();
    let device_context = &context._device_context;

    // Distinct bit-reversed-order monomial coefficients per column.
    let monomials_host: Vec<BF> = (0..num_ntts)
        .flat_map(|col| {
            (0..n).map(move |idx| {
                BF::new(
                    (17 + (idx as u32).wrapping_mul(31) + (col as u32).wrapping_mul(101)) as u32,
                )
            })
        })
        .collect();

    // --- Launcher path (SUBJECT = the DIT engine) ----------------------------
    let mut monomials_dev = context.alloc(num_ntts * n).unwrap();
    let mut out_dev = context.alloc(out_cols * n).unwrap();
    // Test-allocated d-table scratch (len == N). A plain cudaMalloc is fine
    // here; tests are not on the enqueue-only production hot path.
    let mut d_scratch = context.alloc(n).unwrap();
    memory_copy_async(&mut monomials_dev, &monomials_host, stream).unwrap();

    {
        let inputs_matrix = DeviceMatrixChunk::new(&monomials_dev[..], n, 0, n);
        let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut out_dev[..], n, 0, n);
        assert_eq!(inputs_matrix.cols(), num_ntts);
        assert_eq!(outputs_matrix.cols(), out_cols);
        monomials_to_evals_dit(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n as usize,
            log_vpt as usize,
            coset_index_base,
            coset_factor_shift,
            num_cosets,
            num_cols_per_coset,
            false,
            device_context,
            &mut d_scratch[..],
            stream,
            device_props,
        )
        .unwrap();
    }

    let mut engine_host = vec![BF::ZERO; out_cols * n];
    memory_copy_async(&mut engine_host, &out_dev, stream).unwrap();
    stream.synchronize().unwrap();

    // --- Reference (ORACLE) path: compact 1-pass kernel, called DIRECTLY -----
    // Not via `bitreversed_monomials_to_natural_evals` (which now routes the DIT
    // range to the engine under test — that would be circular). Compact reads
    // twiddles from `__constant__` tables, an independent baseline. Both
    // launcher configs (log_n 9 two-pass, log_n 4 single-pass) have log_n <= 12,
    // so 1-pass compact applies.
    let mut monomials_ref_dev = context.alloc(n).unwrap();
    let mut ref_out_dev = context.alloc(n).unwrap();

    for col in 0..num_ntts {
        let col_monomials = &monomials_host[col * n..col * n + n];
        memory_copy_async(&mut monomials_ref_dev, col_monomials, stream).unwrap();

        for k in 0..num_cosets {
            {
                let inputs_matrix = DeviceMatrixChunk::new(&monomials_ref_dev[..], n, 0, n);
                let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut ref_out_dev[..], n, 0, n);
                super::super::ntt::monomials_to_evals_compact_1_pass(
                    &inputs_matrix,
                    &mut outputs_matrix,
                    log_n as usize,
                    k,
                    coset_factor_shift,
                    1,
                    1,
                    1,
                    false,
                    stream,
                )
                .unwrap();
            }
            let mut ref_host = vec![BF::ZERO; n];
            memory_copy_async(&mut ref_host, &ref_out_dev, stream).unwrap();
            stream.synchronize().unwrap();

            let slab_col = k * num_cols_per_coset + col;
            let engine_slab = &engine_host[slab_col * n..slab_col * n + n];
            let mut first_mismatch = None;
            for i in 0..n {
                if engine_slab[i] != ref_host[i] {
                    first_mismatch = Some(i);
                    break;
                }
            }
            if let Some(first_i) = first_mismatch {
                eprintln!(
                    "DIT launcher parity FAIL: log_n={log_n}, log_vpt={log_vpt}, \
                     num_cosets={num_cosets}, num_ntts={num_ntts}, coset={k}, col={col}"
                );
                let mut dumped = 0;
                for i in 0..n {
                    if engine_slab[i] != ref_host[i] {
                        eprintln!(
                            "  (i={i}, got={:?}, expected={:?})",
                            engine_slab[i], ref_host[i]
                        );
                        dumped += 1;
                        if dumped >= 8 {
                            break;
                        }
                    }
                }
                panic!(
                    "DIT launcher parity FAILED: log_n={log_n}, log_vpt={log_vpt}, \
                     num_cosets={num_cosets}, coset={k}, col={col}, first_i={first_i}"
                );
            }
        }
    }

    println!(
        "DIT launcher parity PASS: log_n={log_n}, log_vpt={log_vpt}, \
         num_cosets={num_cosets}, num_ntts={num_ntts} (all (coset,col) slabs match red's oracle)"
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn dit_launcher_two_pass_parity() {
    // Two-pass path (log_n=9, log_vpt=3 → two_pass since 9 > 3+5=8), multi-coset,
    // multi-column, back-to-back strided output (num_cols_per_coset = num_ntts).
    run_launcher_parity(9, 3, 4, 3);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn dit_launcher_single_pass_parity() {
    // Single-pass path (log_n=4, log_vpt=2 → cosets_per_block = 1024/4 = 256).
    // num_cosets=512 → grid = 512/256 = 2; multi-column, strided output.
    run_launcher_parity(4, 2, 512, 2);
}

// ===========================================================================
// BENCH-ONLY DIT kernel VARIANTS — parity for the two NEW templates that the
// bench bring-up added (`ntt_two_pass_fixed<K>`, `ntt_single_stream`).
//
// These symbols are emitted ONLY from `native/bench/dit_bench_kernels.cu`,
// which compiles into `gpu_ntt_native` solely under `-DGPU_NTT_BUILD_BENCH=ON`
// (the gpu_ntt `bench` feature). Linking them outside `--features bench` would
// fail, so the entire section is `#[cfg(feature = "bench")]`.
//
// Both variants are validated against the SAME host oracle the production
// parity tests use; only the launch geometry / ABI differ:
//
//  - `ab_dit_two_pass_fixed_<LOGN>_<VPT>_<K>` — 8-arg ABI, NO runtime
//    `cosets_per_block` (K is a compile-time template arg). Geometry: the grid
//    is `total / K` blocks, each block does EXACTLY K cosets. The d-table step
//    is the SAME as production two-pass (`grid * coset_step`), and the kernel's
//    output coset mapping `(bx + c*gd)` is identical to production two-pass — so
//    `run_two_pass_parity`'s oracle build + per-coset comparison are reused
//    verbatim (only `grid` is derived from K instead of passed in).
//
//  - `ab_dit_single_stream_<LOGN>_<VPT>` — 7-arg ABI with RUNTIME
//    `cosets_per_block`, NO d-table. Geometry: `slots_per_block = 128 / lanes`
//    (`lanes = 1 << (log_n - log_vpt)`, 4 warps = 128 threads), and
//    `cosets_per_block = total / (grid * slots_per_block)`. The kernel maps
//    `coset_idx = blockIdx*slots_per_block + slot + c*(grid*slots_per_block)`,
//    a bijection onto `[0, total)`, so the single-pass per-coset oracle applies
//    unchanged (just with `num_cosets = total`).
// ===========================================================================
#[cfg(feature = "bench")]
mod bench_variants {
    use super::*;

    // --- two_pass_fixed<K> ABI: 8 args, NO cosets_per_block (K compile-time) ---
    cuda_kernel!(
        DitTwoPassFixed,
        dit_two_pass_fixed,
        monomials_bitrev: *const BF,
        tw_p1_coupled: *const BF,
        tw_p2_clean: *const BF,
        d_table: *const BF,
        out_natural: *mut BF,
        cfp_0: u32,
        coset_step: u32,
        coset_out_stride: u32,
    );
    dit_two_pass_fixed!(ab_dit_two_pass_fixed_13_3_8);
    dit_two_pass_fixed!(ab_dit_two_pass_fixed_9_3_4);

    // --- single_stream ABI: 7 args, runtime cosets_per_block, NO d-table -------
    cuda_kernel!(
        DitSingleStream,
        dit_single_stream,
        monomials_bitrev: *const BF,
        tw_clean: *const BF,
        out_natural: *mut BF,
        cfp_0: u32,
        coset_step: u32,
        cosets_per_block: u32,
        coset_out_stride: u32,
    );
    dit_single_stream!(ab_dit_single_stream_8_3);
    dit_single_stream!(ab_dit_single_stream_3_3);

    // -----------------------------------------------------------------------
    // two_pass_fixed<K> parity. Body mirrors `run_two_pass_parity`; the ONLY
    // changes are: `grid = total / k` (derived, not passed); K/grid pow2 +
    // divisibility asserts; the 8-arg `DitTwoPassFixed*Arguments::new` (no
    // `cosets_per_block`); and the per-(log_n,log_vpt,k) symbol dispatch. The
    // d-table step stays `grid * coset_step` and the oracle build + comparison
    // are identical to production two-pass.
    // -----------------------------------------------------------------------
    fn run_two_pass_fixed_parity(log_n: u32, log_vpt: u32, k: u32, total: u32) {
        let g = TwoPassGeom::new(log_n, log_vpt);
        let n: usize = g.n as usize;

        // log_lde_factor satisfies total = 2^log_lde_factor.
        assert!(total.is_power_of_two(), "total must be a power of two");
        let log_lde_factor = total.trailing_zeros();
        assert!(
            log_n + log_lde_factor <= OMEGA_LOG_ORDER,
            "log_n + log_lde_factor must be <= {OMEGA_LOG_ORDER}"
        );

        // K is the compile-time cosets-per-block; grid = total / K. K must be a
        // pow2 divisor of total so grid * K == total exactly (no ragged tail),
        // and grid must itself be a power of two (the coset walk strides by grid).
        assert!(k.is_power_of_two(), "k must be a power of two");
        assert!(
            total % k == 0,
            "k ({k}) must divide total ({total}) exactly"
        );
        let grid: u32 = total / k;
        assert!(
            grid.is_power_of_two(),
            "grid (total/k) must be a power of two"
        );
        assert_eq!(grid * k, total, "grid * k must equal total");

        let coset_step: u32 = 1 << (OMEGA_LOG_ORDER - log_n - log_lde_factor);
        let cfp_0: u32 = 0;
        // SAME as production two-pass: step_per_iter = grid * coset_step.
        let step_per_iter: u32 = grid.wrapping_mul(coset_step);

        let context = make_context();
        let stream = context.get_exec_stream();

        // Bit-reversed-order monomial coefficients shared by all cosets.
        let monomials_host: Vec<BF> = (0..n)
            .map(|idx| BF::new((17 + (idx as u32).wrapping_mul(31)) as u32))
            .collect();

        // --- Engine path -----------------------------------------------------
        let tw_p1_host = build_coupled_triangle(log_n, log_vpt, g.log_n1);
        assert_eq!(
            tw_p1_host.len(),
            coupled_triangle_count(log_n, log_vpt, g.log_n1)
        );
        let tw_p2_host = build_clean_triangle(g.log_n2, log_vpt);
        assert_eq!(tw_p2_host.len(), clean_triangle_count(g.log_n2, log_vpt));
        assert_eq!(tw_p2_host.len(), (1usize << g.log_n2) - 1);
        let d_table_host = build_coset_delta_table(log_n, log_vpt, step_per_iter);
        assert_eq!(d_table_host.len(), n);

        let mut monomials_dev = context.alloc(n).unwrap();
        let mut tw_p1_dev = context.alloc(tw_p1_host.len()).unwrap();
        let mut tw_p2_dev = context.alloc(tw_p2_host.len()).unwrap();
        let mut d_table_dev = context.alloc(d_table_host.len()).unwrap();
        let mut out_dev = context.alloc((total as usize) * n).unwrap();
        memory_copy_async(&mut monomials_dev, &monomials_host, stream).unwrap();
        memory_copy_async(&mut tw_p1_dev, &tw_p1_host, stream).unwrap();
        memory_copy_async(&mut tw_p2_dev, &tw_p2_host, stream).unwrap();
        memory_copy_async(&mut d_table_dev, &d_table_host, stream).unwrap();

        let smem_bytes = ntt_two_pass_smem_bytes(&g);

        {
            let grid_dim: Dim3 = grid.into();
            let block_dim: Dim3 = g.threads.into();
            let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            config.dynamic_smem_bytes = smem_bytes;

            let mono_ptr = monomials_dev[..].as_ptr();
            let tw_p1_ptr = tw_p1_dev[..].as_ptr();
            let tw_p2_ptr = tw_p2_dev[..].as_ptr();
            let d_ptr = d_table_dev[..].as_ptr();
            let out_ptr = (&mut out_dev[..]).as_mut_ptr();
            // coset_out_stride = N keeps the Phase-1 contiguous-output expectation.
            let coset_out_stride: u32 = 1u32 << log_n;
            // 8-arg ABI: NO cosets_per_block (K is a compile-time template arg).
            let args = DitTwoPassFixedArguments::new(
                mono_ptr,
                tw_p1_ptr,
                tw_p2_ptr,
                d_ptr,
                out_ptr,
                cfp_0,
                coset_step,
                coset_out_stride,
            );

            // Resolve the kernel symbol for this (log_n, log_vpt, k).
            let function = match (log_n, log_vpt, k) {
                (13, 3, 8) => DitTwoPassFixedFunction(ab_dit_two_pass_fixed_13_3_8),
                (9, 3, 4) => DitTwoPassFixedFunction(ab_dit_two_pass_fixed_9_3_4),
                _ => panic!(
                    "unsupported two_pass_fixed config (log_n={log_n}, log_vpt={log_vpt}, k={k})"
                ),
            };

            // Dynamic-smem opt-in (mirrors production two-pass): large configs
            // exceed the 48 KB default cap. No-op below the cap.
            let func_ptr = function.as_ptr();
            unsafe {
                cudaFuncSetAttribute(
                    func_ptr,
                    CudaFuncAttribute::MaxDynamicSharedMemorySize,
                    smem_bytes as i32,
                )
                .wrap()
                .unwrap();
            }
            function.launch(&config, &args).unwrap();
        }

        let mut engine_host = vec![BF::ZERO; (total as usize) * n];
        memory_copy_async(&mut engine_host, &out_dev, stream).unwrap();
        stream.synchronize().unwrap();

        // --- Reference (oracle) path — IDENTICAL to production two-pass ------
        let mut monomials_ref_dev = context.alloc(n).unwrap();
        let mut ref_out_dev = context.alloc(n).unwrap();
        memory_copy_async(&mut monomials_ref_dev, &monomials_host, stream).unwrap();

        let oracle_coset_factor_shift = OMEGA_LOG_ORDER - log_n - log_lde_factor;
        for ci in 0..total as usize {
            {
                let inputs_matrix = DeviceMatrixChunk::new(&monomials_ref_dev[..], n, 0, n);
                let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut ref_out_dev[..], n, 0, n);
                if log_n <= 12 {
                    super::super::super::ntt::monomials_to_evals_compact_1_pass(
                        &inputs_matrix,
                        &mut outputs_matrix,
                        log_n as usize,
                        ci,
                        oracle_coset_factor_shift,
                        1,
                        1,
                        1,
                        false,
                        stream,
                    )
                    .unwrap();
                } else {
                    super::super::super::ntt::monomials_to_evals_2_pass_compact_initial(
                        &inputs_matrix,
                        &mut outputs_matrix,
                        log_n as usize,
                        ci,
                        oracle_coset_factor_shift,
                        1,
                        1,
                        1,
                        1,
                        false,
                        stream,
                    )
                    .unwrap();
                }
            }
            let mut ref_host = vec![BF::ZERO; n];
            memory_copy_async(&mut ref_host, &ref_out_dev, stream).unwrap();
            stream.synchronize().unwrap();

            let engine_coset = &engine_host[ci * n..ci * n + n];
            let mut first_mismatch = None;
            for k_idx in 0..n {
                if engine_coset[k_idx] != ref_host[k_idx] {
                    first_mismatch = Some(k_idx);
                    break;
                }
            }
            if let Some(first_k) = first_mismatch {
                eprintln!(
                    "DIT two_pass_fixed parity FAIL: log_n={log_n}, log_vpt={log_vpt}, \
                     k={k}, total={total}, grid={grid}, coset={ci}"
                );
                let mut dumped = 0;
                for k_idx in 0..n {
                    if engine_coset[k_idx] != ref_host[k_idx] {
                        eprintln!(
                            "  (coset={ci}, index={k_idx}, got={:?}, expected={:?})",
                            engine_coset[k_idx], ref_host[k_idx]
                        );
                        dumped += 1;
                        if dumped >= 8 {
                            break;
                        }
                    }
                }
                panic!(
                    "DIT two_pass_fixed parity FAILED: log_n={log_n}, log_vpt={log_vpt}, \
                     k={k}, total={total}, grid={grid}, coset={ci}, first_k={first_k}"
                );
            }
        }

        println!(
            "DIT two_pass_fixed parity PASS: log_n={log_n}, log_vpt={log_vpt}, \
             k={k}, total={total}, grid={grid} (all cosets match red's oracle)"
        );
    }

    // -----------------------------------------------------------------------
    // single_stream parity. Body mirrors `run_single_pass_parity` but with
    // `num_cosets = total` and the streaming geometry: 4 warps (128 threads),
    // `slots_per_block = 128 / lanes`, `cosets_per_block = total / (grid *
    // slots_per_block)`. NO d-table; smem = clean-triangle bytes (same as
    // single-pass). The kernel's coset mapping is a bijection onto `[0, total)`,
    // so the single-pass per-coset oracle (output[coset_idx]) applies unchanged.
    // -----------------------------------------------------------------------
    fn run_single_stream_parity(log_n: u32, log_vpt: u32, grid: u32, total: u32) {
        let n: usize = 1 << log_n;
        let num_cosets = total as usize;
        // log_lde_factor satisfies total = 2^log_lde_factor.
        assert!(total.is_power_of_two(), "total must be a power of two");
        let log_lde_factor = total.trailing_zeros();
        assert_eq!(1usize << log_lde_factor, num_cosets);

        // Streaming geometry: 4 warps = 128 threads; lanes = 1 << (log_n -
        // log_vpt); slots_per_block = 128 / lanes. `grid` is FREE: the guarded
        // kernel maps coset_idx = s + spb*(b + c*grid) and loops while
        // coset_idx < total, which covers [0, total) exactly once for ANY grid
        // (no divisibility needed). cosets_per_block below is informational.
        let lanes: u32 = 1 << (log_n - log_vpt);
        let slots_per_block: u32 = 128 / lanes;
        assert!(grid >= 1, "grid must be >= 1");
        let cosets_per_block: u32 = total / (grid * slots_per_block);

        // coset_step = 2^(OMEGA_LOG_ORDER - log_n - log_lde_factor)
        let coset_step: u32 = 1 << (OMEGA_LOG_ORDER - log_n - log_lde_factor);
        let cfp_0: u32 = 0;

        let context = make_context();
        let stream = context.get_exec_stream();

        // Bit-reversed-order monomial coefficients shared by all cosets.
        let monomials_host: Vec<BF> = (0..n)
            .map(|idx| BF::new((17 + (idx as u32).wrapping_mul(31)) as u32))
            .collect();

        // --- Engine path -----------------------------------------------------
        let tw_clean_host = build_clean_triangle(log_n, log_vpt);
        assert_eq!(tw_clean_host.len(), clean_triangle_count(log_n, log_vpt));
        assert_eq!(tw_clean_host.len(), n - 1);

        let mut monomials_dev = context.alloc(n).unwrap();
        let mut tw_clean_dev = context.alloc(tw_clean_host.len()).unwrap();
        let mut out_dev = context.alloc(num_cosets * n).unwrap();
        memory_copy_async(&mut monomials_dev, &monomials_host, stream).unwrap();
        memory_copy_async(&mut tw_clean_dev, &tw_clean_host, stream).unwrap();

        {
            let grid_dim: Dim3 = grid.into();
            let block_dim: Dim3 = (4u32 * 32u32).into(); // 128 threads = 4 warps
            let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            // smem = clean-triangle bytes (same as single-pass; all < 48 KB).
            config.dynamic_smem_bytes =
                clean_triangle_count(log_n, log_vpt) * std::mem::size_of::<BF>();

            let mono_ptr = monomials_dev[..].as_ptr();
            let tw_ptr = tw_clean_dev[..].as_ptr();
            let out_ptr = (&mut out_dev[..]).as_mut_ptr();
            // coset_out_stride = N keeps the Phase-1 contiguous-output expectation.
            let coset_out_stride: u32 = 1u32 << log_n;
            // 7-arg ABI: runtime num_cosets (guard bound), NO d-table.
            let args = DitSingleStreamArguments::new(
                mono_ptr,
                tw_ptr,
                out_ptr,
                cfp_0,
                coset_step,
                total,
                coset_out_stride,
            );

            // Dispatch to the correct kernel symbol for this (log_n, log_vpt).
            let result = match (log_n, log_vpt) {
                (8, 3) => DitSingleStreamFunction(ab_dit_single_stream_8_3).launch(&config, &args),
                (3, 3) => DitSingleStreamFunction(ab_dit_single_stream_3_3).launch(&config, &args),
                _ => panic!("unsupported single_stream config (log_n={log_n}, log_vpt={log_vpt})"),
            };
            result.unwrap();
        }

        let mut engine_host = vec![BF::ZERO; num_cosets * n];
        memory_copy_async(&mut engine_host, &out_dev, stream).unwrap();
        stream.synchronize().unwrap();

        // --- Reference (oracle) path — IDENTICAL to single-pass --------------
        let mut monomials_ref_dev = context.alloc(n).unwrap();
        let mut ref_out_dev = context.alloc(n).unwrap();
        memory_copy_async(&mut monomials_ref_dev, &monomials_host, stream).unwrap();

        let oracle_coset_factor_shift = OMEGA_LOG_ORDER - log_n - log_lde_factor;
        let device_props = context.get_device_properties();
        for cc in 0..num_cosets {
            {
                let inputs_matrix = DeviceMatrixChunk::new(&monomials_ref_dev[..], n, 0, n);
                let mut outputs_matrix = DeviceMatrixChunkMut::new(&mut ref_out_dev[..], n, 0, n);
                if log_n <= 7 {
                    super::super::super::ntt::bitreversed_monomials_to_natural_evals(
                        &inputs_matrix,
                        &mut outputs_matrix,
                        log_n as usize,
                        log_lde_factor as usize,
                        cc,
                        false,
                        context.device_context(),
                        None,
                        stream,
                        device_props,
                    )
                    .unwrap();
                } else {
                    super::super::super::ntt::monomials_to_evals_compact_1_pass(
                        &inputs_matrix,
                        &mut outputs_matrix,
                        log_n as usize,
                        cc,
                        oracle_coset_factor_shift,
                        1,
                        1,
                        1,
                        false,
                        stream,
                    )
                    .unwrap();
                }
            }
            let mut ref_host = vec![BF::ZERO; n];
            memory_copy_async(&mut ref_host, &ref_out_dev, stream).unwrap();
            stream.synchronize().unwrap();

            let engine_coset = &engine_host[cc * n..cc * n + n];
            let mut first_mismatch = None;
            for k_idx in 0..n {
                if engine_coset[k_idx] != ref_host[k_idx] {
                    first_mismatch = Some(k_idx);
                    break;
                }
            }
            if let Some(first_k) = first_mismatch {
                eprintln!(
                    "DIT single_stream parity FAIL: log_n={log_n}, log_vpt={log_vpt}, \
                     grid={grid}, total={total}, cosets_per_block={cosets_per_block}, \
                     coset={cc}/{num_cosets}"
                );
                for k_idx in 0..n.min(8) {
                    eprintln!(
                        "  k={k_idx:3}  engine={:?}  expected={:?}{}",
                        engine_coset[k_idx],
                        ref_host[k_idx],
                        if engine_coset[k_idx] != ref_host[k_idx] {
                            "  <-- DIFF"
                        } else {
                            ""
                        }
                    );
                }
                panic!(
                    "DIT single_stream parity FAILED: log_n={log_n}, log_vpt={log_vpt}, \
                     grid={grid}, total={total}, coset={cc}, k={first_k}"
                );
            }
        }

        println!(
            "DIT single_stream parity PASS: log_n={log_n}, log_vpt={log_vpt}, \
             grid={grid}, total={total}, cosets_per_block={cosets_per_block} \
             (all match red's oracle)"
        );
    }

    // --- two_pass_fixed<K> tests -------------------------------------------
    // (13,3,K=8): grid = total/8. total=8 → grid=1; total=16 → grid=2.
    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn two_pass_fixed_13_3_k8_parity() {
        run_two_pass_fixed_parity(13, 3, 8, 8); // grid=1, log_n+log_lde = 13+3 = 16 <= 27
        run_two_pass_fixed_parity(13, 3, 8, 16); // grid=2, log_n+log_lde = 13+4 = 17 <= 27
    }

    // (9,3,K=4): grid = total/4. total=4 → grid=1; total=8 → grid=2.
    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn two_pass_fixed_9_3_k4_parity() {
        run_two_pass_fixed_parity(9, 3, 4, 4); // grid=1, log_n+log_lde = 9+2 = 11 <= 27
        run_two_pass_fixed_parity(9, 3, 4, 8); // grid=2, log_n+log_lde = 9+3 = 12 <= 27
    }

    // --- single_stream tests -----------------------------------------------
    // (8,3): lanes=32, slots_per_block=128/32=4. grid=1,total=32 → cpb=8;
    //        grid=2,total=64 → cpb=8.
    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn single_stream_8_3_parity() {
        run_single_stream_parity(8, 3, 1, 32); // grid*spb=4, 32/4=8 cpb; 8+5=13 <= 27
        run_single_stream_parity(8, 3, 2, 64); // grid*spb=8, 64/8=8 cpb; 8+6=14 <= 27
                                               // ragged: grid*spb=12 does NOT divide 32 — exercises the guard.
        run_single_stream_parity(8, 3, 3, 32);
    }

    // (3,3): lanes=1, slots_per_block=128/1=128. grid=1,total=128 → cpb=1.
    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn single_stream_3_3_parity() {
        run_single_stream_parity(3, 3, 1, 128); // grid*spb=128, 128/128=1 cpb; 3+7=10 <= 27
    }
}
