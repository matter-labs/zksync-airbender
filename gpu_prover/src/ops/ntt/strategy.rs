//! Device-properties-driven NTT strategy selection for the prover.
//!
//! `select_ntt_strategy` returns an `NttStrategy` describing how a given
//! `(log_n, num_columns, num_cosets)` NTT should be executed on the active
//! device. Phase A of the WHIR perf work routes the existing
//! `bitreversed_monomials_to_natural_evals` through this selector without
//! behavior change for the supported `log_n` range; Phase B extends the
//! supported range with new compact kernels.

use crate::primitives::context::DeviceProperties;
use crate::primitives::field::BF;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct NttPass {
    pub start_stage: usize,
    pub stage_count: usize,
    pub kernel: NttKernelKind,
}

/// Direction the NTT plan runs in. Forward = bitreversed monomials → natural
/// evals; Inverse = natural evals → bitreversed monomials.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NttDirection {
    Forward,
    Inverse,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NttKernelKind {
    MonomialsToEvalsInitial {
        stages: usize,
    },
    /// Sub-warp register-resident multi-NTT-per-block 1-pass kernel for
    /// `log_n in [1, 5]`. Each thread holds one element in a register; the
    /// butterfly exchange uses `__shfl_xor_sync` instead of smem. For log_n
    /// in [1, 3] an IPB=1 fallback variant covers workloads smaller than
    /// IPB_max (no compact 1-pass kernel exists below log_n=4).
    MonomialsToEvalsSubwarp {
        stages: usize,
        log_instances_per_block: usize,
    },
    /// Smem-packed multi-NTT-per-block 1-pass kernel for `log_n in [6, 8]`.
    /// Each block holds `1 << log_instances_per_block` independent NTT
    /// instances, each assigned `HALF_N = 1 << (stages - 1)` threads. Picked
    /// over the compact 1-pass when the per-launch workload
    /// (`num_cosets * num_columns`) is a power of two >= `1 <<
    /// log_instances_per_block`, so the kernel's gridDim.x divides cleanly.
    MonomialsToEvalsSmemPacked {
        stages: usize,
        log_instances_per_block: usize,
    },
    /// Compact "first K stages" kernel used as pass 1 of 2-pass plans for
    /// `log_n` in [15, 20]. Each block processes a chunk of `2^stages`
    /// consecutive bitreversed inputs with global-index twiddles.
    MonomialsToEvalsFirstCompact {
        stages: usize,
    },
    MonomialsToEvalsNonInitial {
        stages: usize,
    },
    MonomialsToEvalsLast {
        stages: usize,
    },
    /// Inverse 3-pass nonfinal: 8 stages of bitreversed-evals exchange via
    /// `ab_evals_to_monomials_nonfinal_8_stages_kernel`.
    EvalsToMonomialsNonInitial {
        stages: usize,
    },
    /// Inverse 2-pass first kernel: `ab_evals_to_monomials_first_{9,10}_stages_kernel`
    /// (one block does 9 or 10 stages of natural-evals exchange).
    EvalsToMonomialsFirst {
        stages: usize,
    },
    /// Inverse final pass: `ab_evals_to_monomials_{final_K,last_14}_stages_kernel`.
    EvalsToMonomialsFinal {
        stages: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NttStrategy {
    pub passes: Vec<NttPass>,
    pub columns_per_launch: usize,
    pub cosets_per_launch: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NttStrategyError {
    LogNBelowSupported { log_n: usize, min_supported: usize },
}

/// Smallest `log_n` covered by any multistage NTT kernel family.
///
/// The compact 1-pass family covers `[COMPACT_MIN_LOG_N, COMPACT_MAX_LOG_N]`,
/// with sub-warp register-resident kernels handling log_n in [1, 5] and
/// smem-packed kernels handling log_n in [6, 8]. The 2-pass
/// first-K-stages-compact + noninitial_8 kernels cover
/// `[TWO_PASS_COMPACT_MIN_LOG_N, TWO_PASS_COMPACT_MAX_LOG_N]`, and the existing
/// 2-/3-pass kernels cover `[MULTIPASS_MIN_LOG_N, ..]`. Selector returns
/// `Err(LogNBelowSupported)` for `log_n = 0` only (identity NTT = host memcpy).
pub(crate) const MIN_SUPPORTED_LOG_N: usize = 1;
pub(crate) const COMPACT_MIN_LOG_N: usize = 1;
// log_n in [13, 14] move to the 2-pass-compact-initial path: compact-1-pass
// uses a single block per NTT and starves SMs once the per-block working set
// approaches its smem cap; per-stage launch overhead is a smaller cost than
// the SM-occupancy loss in that range.
pub(crate) const COMPACT_MAX_LOG_N: usize = 12;
pub(crate) const TWO_PASS_COMPACT_MIN_LOG_N: usize = 13;
pub(crate) const TWO_PASS_COMPACT_MAX_LOG_N: usize = 20;
pub(crate) const MULTIPASS_MIN_LOG_N: usize = 21;

pub(crate) fn select_ntt_strategy(
    direction: NttDirection,
    log_n: usize,
    num_columns: usize,
    num_cosets: usize,
    cosets_consolidated: bool,
    device_props: &DeviceProperties,
) -> Result<NttStrategy, NttStrategyError> {
    let _ = cosets_consolidated;
    match direction {
        NttDirection::Forward => {
            select_forward_strategy(log_n, num_columns, num_cosets, device_props)
        }
        NttDirection::Inverse => {
            select_inverse_strategy(log_n, num_columns, num_cosets, device_props)
        }
    }
}

/// Pick the smem-packed multi-NTT-per-block kernel's `log_instances_per_block`
/// when it beats the compact 1-pass kernel; `None` means fall back to compact.
///
/// The kernel uses `HALF_N << log_ipb = (1 << (log_n - 1 + log_ipb))` threads
/// per block. We size IPB so block_threads = 256 (the compact kernel's thread
/// count) for log_n in [6, 8] -- this restores full SM utilization at the
/// log_n range where compact leaves >= 50% of the block idle. log_n >= 9
/// already saturates the block at IPB=1, so the smem-packed variant offers
/// no win there. The kernel's `gridDim.x = (num_cosets * num_columns) >>
/// log_ipb` requires the workload to be a power-of-two multiple of IPB.
fn smem_packed_log_instances_per_block(
    log_n: usize,
    num_columns: usize,
    num_cosets: usize,
) -> Option<usize> {
    // Only the (log_n, log_ipb) pairs below have a corresponding CUDA kernel
    // registered. Smaller workloads than the per-log_n IPB fall back to the
    // compact 1-pass kernel rather than launching a half-empty smem-packed
    // block (which would either underutilize threads or require an additional
    // kernel registration with no perf benefit).
    let log_ipb = match log_n {
        6 => 3, // IPB=8: HALF_N=32  * 8 = 256 threads
        7 => 2, // IPB=4: HALF_N=64  * 4 = 256 threads
        8 => 1, // IPB=2: HALF_N=128 * 2 = 256 threads
        _ => return None,
    };
    if !num_columns.is_power_of_two() || !num_cosets.is_power_of_two() {
        return None;
    }
    let log_workload = num_columns.trailing_zeros() as usize + num_cosets.trailing_zeros() as usize;
    if log_workload < log_ipb {
        return None;
    }
    Some(log_ipb)
}

/// Pick the sub-warp register-resident kernel's `log_instances_per_block` for
/// `log_n in [1, 5]`. The kernel avoids smem entirely by holding one element
/// per thread in a register and exchanging butterfly partners via
/// `__shfl_xor_sync`. For log_n in [1, 3] an IPB=1 variant covers workloads
/// smaller than IPB_max (no compact 1-pass kernel exists below log_n=4 for a
/// fallback). For log_n in [4, 5] the selector returns `None` when workload
/// < IPB_max; compact 1-pass handles those.
fn subwarp_log_instances_per_block(
    log_n: usize,
    num_columns: usize,
    num_cosets: usize,
) -> Option<usize> {
    // log_n in [1, 5]: IPB_max keeps BLOCK_THREADS = 256 by trading off
    // THREADS_PER_INSTANCE = N against IPB. log_n in [1, 3] additionally
    // registers an IPB=1 variant so workloads smaller than IPB_max don't
    // need a compact 1-pass fallback (which only exists for log_n >= 4).
    let log_ipb_max = match log_n {
        1 => 7, // IPB=128: THREADS_PER_INSTANCE=2  * 128 = 256 threads
        2 => 6, // IPB=64 : THREADS_PER_INSTANCE=4  * 64  = 256 threads
        3 => 5, // IPB=32 : THREADS_PER_INSTANCE=8  * 32  = 256 threads
        4 => 4, // IPB=16 : THREADS_PER_INSTANCE=16 * 16  = 256 threads
        5 => 3, // IPB=8  : THREADS_PER_INSTANCE=32 * 8   = 256 threads
        _ => return None,
    };
    if !num_columns.is_power_of_two() || !num_cosets.is_power_of_two() {
        return None;
    }
    let log_workload = num_columns.trailing_zeros() as usize + num_cosets.trailing_zeros() as usize;
    if log_workload >= log_ipb_max {
        return Some(log_ipb_max);
    }
    // log_n in [1, 3] has an IPB=1 fallback kernel for small workloads.
    // log_n in [4, 5] would need to fall back to compact 1-pass instead.
    if log_n <= 3 {
        Some(0)
    } else {
        None
    }
}

/// Joint forward-NTT `(cols_per_launch, cosets_per_launch)` selection.
///
/// **L2 model** for monomials -> multi-coset evals. The caller batches
/// `cols_per_launch` columns at a time and sweeps `num_cosets` cosets in an
/// inner loop; within one kernel launch, K = `cosets_per_launch` cosets run in
/// parallel reading the SAME monomial source. Concurrent L2 demand per launch:
///
///   1 monomial source  + K coset working sets  = (K + 1) * cols * col_bytes
///
/// (the monomial buffer and a per-coset pass-1 intermediate are the same size
/// -- one column's worth of BFs per slot). Across the coset sweep, the
/// monomial source must stay resident for hits from the 2nd launch onward, so
/// we cap `cols * col_bytes <= L2 / 2` (monomials in <= half of L2). The
/// remaining `L2 - cols * col_bytes` is the working-set budget; K is the
/// largest power-of-2 fitting that budget (bounded by `num_cosets`).
///
/// **Optimization objective**: maximize K * cols (per-launch parallelism =
/// fewer total launches across the whole multi-coset NTT). On ties, prefer
/// max `cols`: with the col-outer/coset-inner dispatch loop, fewer col tiles
/// means fewer monomial DRAM reload events at col-tile boundaries.
///
/// **Overflow fallback**: when `col_bytes > L2 / 2` (e.g. log_n=24 on the
/// 5090's 96 MiB L2), no (cols >= 1, K >= 1) pair satisfies the half-L2
/// monomial cap. We return (1, 1) and accept that the launch's working set
/// will overflow L2 -- the alternative would be to refuse to run.
///
/// Empirically validated by `ntt_l2_pressure_sweep_log_n_20` on both the RTX
/// PRO 6000 Blackwell Server (128 MiB L2) and the RTX 5090 (96 MiB L2), where
/// the per-NTT cost minimum landed precisely at working_set = 50% of L2.
fn pick_cols_and_cosets_per_launch(
    log_n: usize,
    num_columns: usize,
    num_cosets: usize,
    device_props: &DeviceProperties,
) -> (usize, usize) {
    let column_bytes = (1usize << log_n) * size_of::<BF>();
    let l2 = device_props.l2_cache_size_bytes;
    let half_l2 = l2 / 2;

    let mut best_cols = 1usize;
    let mut best_k = 1usize;
    let mut best_score = 0usize; // K * cols
    let mut found_valid = false;

    for cols in 1..=num_columns {
        let monomial_bytes = cols * column_bytes;
        if monomial_bytes > half_l2 {
            // Larger `cols` only makes the half-L2 cap worse; further iterations are pointless.
            break;
        }
        // K such that (K + 1) * cols * col_bytes <= L2  <=>  K * monomial_bytes <= l2 - monomial_bytes.
        let k_raw = (l2 / monomial_bytes).saturating_sub(1);
        let k_capped = k_raw.min(num_cosets);
        if k_capped == 0 {
            continue;
        }
        let k_pow2 = 1usize << k_capped.ilog2();
        let score = k_pow2 * cols;
        if score > best_score || (score == best_score && cols > best_cols) {
            best_score = score;
            best_cols = cols;
            best_k = k_pow2;
            found_valid = true;
        }
    }

    if !found_valid {
        // col_bytes > L2/2: even cols=1 doesn't satisfy the half-L2 monomial cap.
        // Accept the overflow -- monomials + one coset working set will exceed L2,
        // but there is no smaller config to fall back to.
        return (1, 1);
    }

    (best_cols, best_k)
}

/// Single-coset column-clamping for the inverse NTT (cosets_per_launch is
/// always 1 -- inverse is a per-column evals -> monomials transform with no
/// coset axis). With K = 1 the joint formula `(K + 1) * cols * col_bytes <= L2`
/// reduces to `cols * col_bytes <= L2/2`. See `pick_cols_and_cosets_per_launch`
/// for the multi-coset forward analog.
fn l2_clamped_columns_per_launch(
    log_n: usize,
    num_columns: usize,
    device_props: &DeviceProperties,
) -> usize {
    let column_bytes = (1usize << log_n) * size_of::<BF>();
    let half_l2 = device_props.l2_cache_size_bytes / 2;
    let columns_per_launch_l2 = if column_bytes == 0 {
        num_columns
    } else {
        (half_l2 / column_bytes).max(1)
    };
    num_columns.min(columns_per_launch_l2)
}

fn select_forward_strategy(
    log_n: usize,
    num_columns: usize,
    num_cosets: usize,
    device_props: &DeviceProperties,
) -> Result<NttStrategy, NttStrategyError> {
    if log_n < COMPACT_MIN_LOG_N {
        return Err(NttStrategyError::LogNBelowSupported {
            log_n,
            min_supported: COMPACT_MIN_LOG_N,
        });
    }
    if (COMPACT_MIN_LOG_N..=COMPACT_MAX_LOG_N).contains(&log_n) {
        // At log_n in {4, 5} the NTT fits within a warp; the sub-warp kernel
        // runs entirely in registers using `__shfl_xor_sync` for butterfly
        // partner exchange (no smem, no syncthreads), strictly cheaper than
        // the smem-packed variant when applicable. Falls through to
        // smem-packed / compact when the per-launch workload is smaller than
        // the required IPB.
        if let Some(log_ipb) = subwarp_log_instances_per_block(log_n, num_columns, num_cosets) {
            return Ok(NttStrategy {
                passes: vec![NttPass {
                    start_stage: 0,
                    stage_count: log_n,
                    kernel: NttKernelKind::MonomialsToEvalsSubwarp {
                        stages: log_n,
                        log_instances_per_block: log_ipb,
                    },
                }],
                columns_per_launch: num_columns,
                cosets_per_launch: num_cosets,
            });
        }
        // At log_n in [6, 8] the compact 1-pass kernel leaves 87.5/75/50% of
        // its 256 block threads idle in butterfly stages (HALF_N = 32/64/128).
        // Pack multiple NTT instances per block (IPB = 8/4/2) when the
        // per-launch workload `num_cosets * num_columns` is divisible by IPB
        // and the kernel's grid factoring lines up. This restores full block
        // utilization at the log_n range used by recursive WHIR + small folds.
        if let Some(log_ipb) = smem_packed_log_instances_per_block(log_n, num_columns, num_cosets) {
            return Ok(NttStrategy {
                passes: vec![NttPass {
                    start_stage: 0,
                    stage_count: log_n,
                    kernel: NttKernelKind::MonomialsToEvalsSmemPacked {
                        stages: log_n,
                        log_instances_per_block: log_ipb,
                    },
                }],
                columns_per_launch: num_columns,
                cosets_per_launch: num_cosets,
            });
        }
        // Single-launch all-stages-in-block kernel. No inter-pass reuse means
        // L2 isn't binding, so we batch every coset into `gridDim.x` to
        // eliminate the per-coset launch overhead that dominates this range
        // at production num_cosets (= lde_factor, up to 2^19).
        return Ok(NttStrategy {
            passes: vec![NttPass {
                start_stage: 0,
                stage_count: log_n,
                kernel: NttKernelKind::MonomialsToEvalsInitial { stages: log_n },
            }],
            columns_per_launch: num_columns,
            cosets_per_launch: num_cosets,
        });
    }
    if (TWO_PASS_COMPACT_MIN_LOG_N..=TWO_PASS_COMPACT_MAX_LOG_N).contains(&log_n) {
        // 2-pass: first K stages (K = log_n - 8) via compact-style kernel +
        // noninitial 8 stages. Pass 1 writes pass-2's input; the per-launch
        // working set plus the monomial source must fit in L2 across the
        // coset-tile sweep. The joint optimizer picks
        // `(cols_per_launch, cosets_per_launch)` to maximize per-launch
        // parallelism `K * cols` under `(K + 1) * cols * col_bytes <= L2`,
        // tie-breaking on max cols.
        let initial_stages = log_n - 8;
        let (columns_per_launch, cosets_per_launch) =
            pick_cols_and_cosets_per_launch(log_n, num_columns, num_cosets, device_props);
        return Ok(NttStrategy {
            passes: vec![
                NttPass {
                    start_stage: 0,
                    stage_count: initial_stages,
                    kernel: NttKernelKind::MonomialsToEvalsFirstCompact {
                        stages: initial_stages,
                    },
                },
                NttPass {
                    start_stage: initial_stages,
                    stage_count: 8,
                    kernel: NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 },
                },
            ],
            columns_per_launch,
            cosets_per_launch,
        });
    }
    let column_bytes = (1usize << log_n) * size_of::<BF>();
    let use_two_pass = column_bytes >= device_props.l2_cache_size_bytes && log_n >= 23;
    let passes = if use_two_pass {
        let final_stages = log_n - 14;
        vec![
            NttPass {
                start_stage: 0,
                stage_count: 14,
                kernel: NttKernelKind::MonomialsToEvalsInitial { stages: 14 },
            },
            NttPass {
                start_stage: 14,
                stage_count: final_stages,
                kernel: NttKernelKind::MonomialsToEvalsLast {
                    stages: final_stages,
                },
            },
        ]
    } else {
        let initial_stages = log_n - 16;
        vec![
            NttPass {
                start_stage: 0,
                stage_count: initial_stages,
                kernel: NttKernelKind::MonomialsToEvalsInitial {
                    stages: initial_stages,
                },
            },
            NttPass {
                start_stage: initial_stages,
                stage_count: 8,
                kernel: NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 },
            },
            NttPass {
                start_stage: initial_stages + 8,
                stage_count: 8,
                kernel: NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 },
            },
        ]
    };
    // 3-pass (log_n in [21, 24]) and 2-pass `use_two_pass` (log_n in [23, 24]
    // when one column alone exceeds L2): joint
    // `(cols_per_launch, cosets_per_launch)` selection from the unified
    // (K + 1) * cols * col_bytes <= L2 budget. See
    // `pick_cols_and_cosets_per_launch`.
    let (columns_per_launch, cosets_per_launch) =
        pick_cols_and_cosets_per_launch(log_n, num_columns, num_cosets, device_props);
    Ok(NttStrategy {
        passes,
        columns_per_launch,
        cosets_per_launch,
    })
}

/// Inverse strategy: only the multi-pass range (`log_n >= 21`) goes through
/// here; callers handle the per-stage fallback for `log_n < 21` themselves.
fn select_inverse_strategy(
    log_n: usize,
    num_columns: usize,
    num_cosets: usize,
    device_props: &DeviceProperties,
) -> Result<NttStrategy, NttStrategyError> {
    let _ = num_cosets;
    if log_n < MULTIPASS_MIN_LOG_N {
        return Err(NttStrategyError::LogNBelowSupported {
            log_n,
            min_supported: MULTIPASS_MIN_LOG_N,
        });
    }
    let column_bytes = (1usize << log_n) * size_of::<BF>();
    let use_two_pass = column_bytes >= device_props.l2_cache_size_bytes && log_n >= 23;
    let passes = if use_two_pass {
        let first_stages = log_n - 14;
        vec![
            NttPass {
                start_stage: 0,
                stage_count: first_stages,
                kernel: NttKernelKind::EvalsToMonomialsFirst {
                    stages: first_stages,
                },
            },
            NttPass {
                start_stage: first_stages,
                stage_count: 14,
                kernel: NttKernelKind::EvalsToMonomialsFinal { stages: 14 },
            },
        ]
    } else {
        let final_stages = log_n - 16;
        vec![
            NttPass {
                start_stage: 0,
                stage_count: 8,
                kernel: NttKernelKind::EvalsToMonomialsNonInitial { stages: 8 },
            },
            NttPass {
                start_stage: 8,
                stage_count: 8,
                kernel: NttKernelKind::EvalsToMonomialsNonInitial { stages: 8 },
            },
            NttPass {
                start_stage: 16,
                stage_count: final_stages,
                kernel: NttKernelKind::EvalsToMonomialsFinal {
                    stages: final_stages,
                },
            },
        ]
    };
    Ok(NttStrategy {
        passes,
        columns_per_launch: l2_clamped_columns_per_launch(log_n, num_columns, device_props),
        cosets_per_launch: 1,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn l4_like() -> DeviceProperties {
        // L4-class device: 48 MB L2, 58 SMs. Numbers documented inline so the
        // snapshot tests stay valid even if `DeviceProperties::new()` reads a
        // different device at test time.
        DeviceProperties {
            l2_cache_size_bytes: 48 * 1024 * 1024,
            sm_count: 58,
        }
    }

    fn rtx_5090_like() -> DeviceProperties {
        // RTX 5090-class device: ~96 MB L2, 170 SMs.
        DeviceProperties {
            l2_cache_size_bytes: 96 * 1024 * 1024,
            sm_count: 170,
        }
    }

    #[test]
    fn ntt_strategy_round_trips_through_constructors() {
        let strategy = NttStrategy {
            passes: vec![
                NttPass {
                    start_stage: 0,
                    stage_count: 5,
                    kernel: NttKernelKind::MonomialsToEvalsInitial { stages: 5 },
                },
                NttPass {
                    start_stage: 5,
                    stage_count: 8,
                    kernel: NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 },
                },
                NttPass {
                    start_stage: 13,
                    stage_count: 8,
                    kernel: NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 },
                },
            ],
            columns_per_launch: 1,
            cosets_per_launch: 1,
        };
        assert_eq!(strategy.passes.len(), 3);
        assert_eq!(
            strategy.passes.iter().map(|p| p.stage_count).sum::<usize>(),
            21
        );
        assert_eq!(strategy.columns_per_launch, 1);
    }

    #[test]
    fn log_n_24_picks_two_pass_when_column_exceeds_l2() {
        // 2^24 * 4 bytes = 64 MB; > L4's 48 MB L2 -> 2-pass.
        let s = select_ntt_strategy(NttDirection::Forward, 24, 1, 1, false, &l4_like()).unwrap();
        assert_eq!(s.passes.len(), 2);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 14 }
        ));
        assert!(matches!(
            s.passes[1].kernel,
            NttKernelKind::MonomialsToEvalsLast { stages: 10 }
        ));
        assert_eq!(s.passes.iter().map(|p| p.stage_count).sum::<usize>(), 24);
    }

    #[test]
    fn log_n_24_picks_three_pass_when_column_fits_l2() {
        // 64 MB column fits in RTX 5090's 96 MB L2 -> 3-pass.
        let s =
            select_ntt_strategy(NttDirection::Forward, 24, 1, 1, false, &rtx_5090_like()).unwrap();
        assert_eq!(s.passes.len(), 3);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 8 }
        ));
    }

    #[test]
    fn log_n_21_picks_three_pass_with_initial_5_stages() {
        let s = select_ntt_strategy(NttDirection::Forward, 21, 1, 1, false, &l4_like()).unwrap();
        assert_eq!(s.passes.len(), 3);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 5 }
        ));
        assert_eq!(s.passes.iter().map(|p| p.stage_count).sum::<usize>(), 21);
    }

    #[test]
    fn log_n_below_1_returns_below_supported() {
        let err =
            select_ntt_strategy(NttDirection::Forward, 0, 1, 1, false, &l4_like()).unwrap_err();
        assert_eq!(
            err,
            NttStrategyError::LogNBelowSupported {
                log_n: 0,
                min_supported: COMPACT_MIN_LOG_N,
            }
        );
    }

    #[test]
    fn two_pass_compact_range_emits_first_compact_plus_noninitial_8() {
        for log_n in TWO_PASS_COMPACT_MIN_LOG_N..=TWO_PASS_COMPACT_MAX_LOG_N {
            let s =
                select_ntt_strategy(NttDirection::Forward, log_n, 1, 1, false, &l4_like()).unwrap();
            assert_eq!(s.passes.len(), 2, "log_n={log_n}");
            let initial_stages = log_n - 8;
            assert_eq!(s.passes[0].start_stage, 0, "log_n={log_n}");
            assert_eq!(s.passes[0].stage_count, initial_stages, "log_n={log_n}");
            assert!(
                matches!(
                    s.passes[0].kernel,
                    NttKernelKind::MonomialsToEvalsFirstCompact { stages } if stages == initial_stages
                ),
                "log_n={log_n}, kernel={:?}",
                s.passes[0].kernel
            );
            assert_eq!(s.passes[1].start_stage, initial_stages, "log_n={log_n}");
            assert_eq!(s.passes[1].stage_count, 8, "log_n={log_n}");
            assert!(matches!(
                s.passes[1].kernel,
                NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 }
            ));
            assert_eq!(s.passes.iter().map(|p| p.stage_count).sum::<usize>(), log_n);
        }
    }

    #[test]
    fn compact_range_emits_single_pass_strategy() {
        for log_n in COMPACT_MIN_LOG_N..=COMPACT_MAX_LOG_N {
            let s =
                select_ntt_strategy(NttDirection::Forward, log_n, 1, 1, false, &l4_like()).unwrap();
            assert_eq!(s.passes.len(), 1, "log_n={log_n}");
            let pass = &s.passes[0];
            assert_eq!(pass.start_stage, 0, "log_n={log_n}");
            assert_eq!(pass.stage_count, log_n, "log_n={log_n}");
            // log_n in [1, 3] picks subwarp with IPB=1 (the small-workload
            // fallback for log_n that has no compact 1-pass kernel registered);
            // log_n in [4, 5] falls through to the compact 1-pass kernel at
            // workload=1; log_n in [6, 12] uses compact 1-pass directly.
            let expected_kind = match log_n {
                1 | 2 | 3 => format!(
                    "MonomialsToEvalsSubwarp {{ stages: {log_n}, log_instances_per_block: 0 }}"
                ),
                _ => format!("MonomialsToEvalsInitial {{ stages: {log_n} }}"),
            };
            assert_eq!(format!("{:?}", pass.kernel), expected_kind, "log_n={log_n}",);
            assert_eq!(s.columns_per_launch, 1);
            assert_eq!(s.cosets_per_launch, 1);
        }
    }

    #[test]
    fn smem_packed_picked_for_log_n_6_7_8_when_workload_supports_it() {
        // For log_n in [6, 8] the smem-packed kernel kicks in once
        // `num_cosets * num_columns` is a power of two >= the per-log_n IPB
        // max (8 / 4 / 2). The fallback (compact 1-pass) covers the boundary
        // cases (single-coset single-column, or non-power-of-two workloads).
        let l4 = l4_like();
        // log_n=6, IPB_max=8.
        let s = select_ntt_strategy(NttDirection::Forward, 6, 4, 4, false, &l4).unwrap();
        assert_eq!(s.passes.len(), 1);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsSmemPacked {
                stages: 6,
                log_instances_per_block: 3
            }
        ));
        assert_eq!(s.cosets_per_launch, 4);
        assert_eq!(s.columns_per_launch, 4);
        // log_n=7, IPB_max=4.
        let s = select_ntt_strategy(NttDirection::Forward, 7, 4, 4, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsSmemPacked {
                stages: 7,
                log_instances_per_block: 2
            }
        ));
        // log_n=8, IPB_max=2.
        let s = select_ntt_strategy(NttDirection::Forward, 8, 4, 4, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsSmemPacked {
                stages: 8,
                log_instances_per_block: 1
            }
        ));
        // log_n=9: no smem-packed (HALF_N=256 already saturates the block).
        let s = select_ntt_strategy(NttDirection::Forward, 9, 4, 4, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 9 }
        ));
        // workload=1 (single coset, single column): fallback to compact 1-pass.
        let s = select_ntt_strategy(NttDirection::Forward, 7, 1, 1, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 7 }
        ));
        // log_n=6, workload=4 (< IPB=8): fallback to compact 1-pass. The
        // selector intentionally does not emit a smaller-IPB smem-packed
        // variant because no such kernel is registered (and a half-empty
        // smem-packed block would not beat compact 1-pass).
        let s = select_ntt_strategy(NttDirection::Forward, 6, 4, 1, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 6 }
        ));
        // log_n=7, workload=2 (< IPB=4): fallback to compact 1-pass.
        let s = select_ntt_strategy(NttDirection::Forward, 7, 2, 1, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 7 }
        ));
    }

    #[test]
    fn subwarp_picked_for_log_n_4_5_when_workload_supports_it() {
        // Sub-warp kernel covers log_n in {4, 5}; IPB_max = 16 / 8 -> requires
        // log_workload >= 4 / 3 respectively. Below that we fall back through
        // smem-packed (which doesn't cover 4/5) to compact 1-pass.
        let l4 = l4_like();
        // log_n=5, num_cosets=8 (log_workload=3 == IPB=8).
        let s = select_ntt_strategy(NttDirection::Forward, 5, 1, 8, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsSubwarp {
                stages: 5,
                log_instances_per_block: 3
            }
        ));
        assert_eq!(s.cosets_per_launch, 8);
        assert_eq!(s.columns_per_launch, 1);
        // log_n=4, num_cosets=16 (log_workload=4 == IPB=16).
        let s = select_ntt_strategy(NttDirection::Forward, 4, 1, 16, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsSubwarp {
                stages: 4,
                log_instances_per_block: 4
            }
        ));
        // log_n=4, num_cosets=4 (log_workload=2 < IPB=16): falls back to
        // compact 1-pass (smem-packed doesn't cover log_n<6 either).
        let s = select_ntt_strategy(NttDirection::Forward, 4, 1, 4, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 4 }
        ));
        // log_n=5, single-coset / single-column: workload=1, falls back to
        // compact 1-pass.
        let s = select_ntt_strategy(NttDirection::Forward, 5, 1, 1, false, &l4).unwrap();
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::MonomialsToEvalsInitial { stages: 5 }
        ));
        // log_n in [1, 3] with workload < IPB_max stays on subwarp with
        // log_ipb=0 (IPB=1) -- no compact 1-pass kernel exists below log_n=4.
        for log_n in 1..=3 {
            let s = select_ntt_strategy(NttDirection::Forward, log_n, 1, 1, false, &l4).unwrap();
            assert!(
                matches!(
                    s.passes[0].kernel,
                    NttKernelKind::MonomialsToEvalsSubwarp {
                        stages,
                        log_instances_per_block: 0
                    } if stages == log_n
                ),
                "log_n={log_n}, kernel={:?}",
                s.passes[0].kernel,
            );
        }
    }

    #[test]
    fn compact_range_batches_all_cosets_into_one_launch() {
        // Compact 1-pass has no inter-pass L2 reuse, so cosets_per_launch
        // follows num_cosets and feeds straight into gridDim.x.
        for num_cosets in [1usize, 2, 8, 128, 1 << 19] {
            for log_n in COMPACT_MIN_LOG_N..=COMPACT_MAX_LOG_N {
                let s = select_ntt_strategy(
                    NttDirection::Forward,
                    log_n,
                    1,
                    num_cosets,
                    false,
                    &l4_like(),
                )
                .unwrap();
                assert_eq!(
                    s.cosets_per_launch, num_cosets,
                    "compact 1-pass: log_n={log_n}, num_cosets={num_cosets}",
                );
            }
        }
    }

    #[test]
    fn columns_per_launch_full_batching_in_compact_ranges() {
        // For compact 1-pass and 2-pass-compact-initial ranges the per-tile
        // working set is comfortably under L2, so `columns_per_launch ==
        // num_columns` regardless of column count.
        for num_columns in [1usize, 2, 4] {
            for log_n in COMPACT_MIN_LOG_N..=COMPACT_MAX_LOG_N {
                let s = select_ntt_strategy(
                    NttDirection::Forward,
                    log_n,
                    num_columns,
                    1,
                    false,
                    &l4_like(),
                )
                .unwrap();
                assert_eq!(
                    s.columns_per_launch, num_columns,
                    "compact 1-pass: log_n={log_n}, num_columns={num_columns}",
                );
            }
            for log_n in TWO_PASS_COMPACT_MIN_LOG_N..=TWO_PASS_COMPACT_MAX_LOG_N {
                let s = select_ntt_strategy(
                    NttDirection::Forward,
                    log_n,
                    num_columns,
                    1,
                    false,
                    &l4_like(),
                )
                .unwrap();
                assert_eq!(
                    s.columns_per_launch, num_columns,
                    "2-pass compact-initial: log_n={log_n}, num_columns={num_columns}",
                );
            }
        }
    }

    #[test]
    fn columns_per_launch_l2_clamped_in_multipass_range() {
        // L4-like: 48 MB L2, working-set budget = 50% = 24 MB. Per-column
        // footprint = (1 << log_n) * 4 bytes (just pass-1's output -- input
        // streams through ld.cs). columns_per_launch = min(num_columns, max(1,
        // budget / column_bytes)).
        // log_n=21: column_bytes = 8 MB, budget / col = 3 -> min(4, 3) = 3.
        // log_n=22: column_bytes = 16 MB, budget / col = 1 -> min(4, 1) = 1.
        // log_n=23: column_bytes = 32 MB, budget / col = 0 -> max(1) = 1 -> 1.
        // log_n=24: column_bytes = 64 MB, budget / col = 0 -> max(1) = 1 -> 1.
        let l4 = l4_like();
        assert_eq!(
            select_ntt_strategy(NttDirection::Forward, 21, 4, 1, false, &l4)
                .unwrap()
                .columns_per_launch,
            3,
            "log_n=21 should batch 3 columns on L4 (budget 24 MB / 8 MB = 3)",
        );
        assert_eq!(
            select_ntt_strategy(NttDirection::Forward, 22, 4, 1, false, &l4)
                .unwrap()
                .columns_per_launch,
            1,
            "log_n=22 should drop to 1 on L4 (budget 24 MB / 16 MB = 1)",
        );
        assert_eq!(
            select_ntt_strategy(NttDirection::Forward, 23, 4, 1, false, &l4)
                .unwrap()
                .columns_per_launch,
            1,
            "log_n=23 should drop to 1 (budget 24 MB < 32 MB column)",
        );
        assert_eq!(
            select_ntt_strategy(NttDirection::Forward, 24, 4, 1, false, &l4)
                .unwrap()
                .columns_per_launch,
            1,
            "log_n=24 should drop to 1 (column exceeds budget)",
        );
        // num_columns=1 always returns 1.
        for log_n in MULTIPASS_MIN_LOG_N..=24 {
            assert_eq!(
                select_ntt_strategy(NttDirection::Forward, log_n, 1, 1, false, &l4)
                    .unwrap()
                    .columns_per_launch,
                1,
                "single-column caller stays at 1 regardless of L2: log_n={log_n}",
            );
        }
    }

    #[test]
    fn joint_cols_cosets_per_launch_with_multi_coset_workload() {
        // L4-like: 48 MB L2, num_cols=4, large num_cosets. Joint optimizer
        // maximizes `K * cols` under `(K + 1) * cols * col_bytes <= L2`,
        // tie-breaking on max cols.
        // log_n=21 (col_bytes=8 MB): cols=1,K=4 (5*8=40) and cols=2,K=2 (3*16=48)
        //                            both score 4; tie-break -> (2, 2).
        // log_n=22 (col_bytes=16 MB): cols=1,K=2 (3*16=48) is sole valid; cols=2
        //                             would need 32 MB monomials > L2/2=24 MB.
        // log_n=23 (col_bytes=32 MB): cols=1 needs 32 MB monomials > L2/2=24 MB.
        //                             Fallback (1, 1) -- single coset overflows.
        // log_n=24 (col_bytes=64 MB): same overflow -> (1, 1).
        let l4 = l4_like();
        let cases: &[(usize, usize, usize)] =
            &[(21, 2, 2), (22, 1, 2), (23, 1, 1), (24, 1, 1)];
        for &(log_n, expected_cols, expected_cosets) in cases {
            let s =
                select_ntt_strategy(NttDirection::Forward, log_n, 4, 64, false, &l4).unwrap();
            assert_eq!(
                s.columns_per_launch, expected_cols,
                "log_n={log_n} (num_cosets=64): cols mismatch",
            );
            assert_eq!(
                s.cosets_per_launch, expected_cosets,
                "log_n={log_n} (num_cosets=64): cosets mismatch",
            );
        }
    }

    #[test]
    fn inverse_below_multipass_min_returns_below_supported() {
        // Inverse only supports log_n >= 21 (the multistage range); callers
        // handle the per-stage fallback for smaller log_n.
        for log_n in 0..MULTIPASS_MIN_LOG_N {
            let err = select_ntt_strategy(NttDirection::Inverse, log_n, 1, 1, false, &l4_like())
                .unwrap_err();
            assert_eq!(
                err,
                NttStrategyError::LogNBelowSupported {
                    log_n,
                    min_supported: MULTIPASS_MIN_LOG_N,
                },
                "log_n={log_n}",
            );
        }
    }

    #[test]
    fn inverse_log_n_24_picks_two_pass_when_column_exceeds_l2() {
        // 2^24 * 4 bytes = 64 MB; > L4's 48 MB L2 -> inverse 2-pass:
        // EvalsToMonomialsFirst(10) + EvalsToMonomialsFinal(14).
        let s = select_ntt_strategy(NttDirection::Inverse, 24, 1, 1, false, &l4_like()).unwrap();
        assert_eq!(s.passes.len(), 2);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::EvalsToMonomialsFirst { stages: 10 }
        ));
        assert_eq!(s.passes[0].start_stage, 0);
        assert!(matches!(
            s.passes[1].kernel,
            NttKernelKind::EvalsToMonomialsFinal { stages: 14 }
        ));
        assert_eq!(s.passes[1].start_stage, 10);
        assert_eq!(s.passes.iter().map(|p| p.stage_count).sum::<usize>(), 24);
    }

    #[test]
    fn inverse_log_n_24_picks_three_pass_when_column_fits_l2() {
        // 64 MB fits in RTX 5090's 96 MB L2 -> inverse 3-pass.
        let s =
            select_ntt_strategy(NttDirection::Inverse, 24, 1, 1, false, &rtx_5090_like()).unwrap();
        assert_eq!(s.passes.len(), 3);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::EvalsToMonomialsNonInitial { stages: 8 }
        ));
        assert!(matches!(
            s.passes[1].kernel,
            NttKernelKind::EvalsToMonomialsNonInitial { stages: 8 }
        ));
        assert!(matches!(
            s.passes[2].kernel,
            NttKernelKind::EvalsToMonomialsFinal { stages: 8 }
        ));
        assert_eq!(s.passes.iter().map(|p| p.stage_count).sum::<usize>(), 24);
    }

    #[test]
    fn inverse_log_n_21_picks_three_pass_with_final_5_stages() {
        let s = select_ntt_strategy(NttDirection::Inverse, 21, 1, 1, false, &l4_like()).unwrap();
        assert_eq!(s.passes.len(), 3);
        assert!(matches!(
            s.passes[0].kernel,
            NttKernelKind::EvalsToMonomialsNonInitial { stages: 8 }
        ));
        assert!(matches!(
            s.passes[1].kernel,
            NttKernelKind::EvalsToMonomialsNonInitial { stages: 8 }
        ));
        assert!(matches!(
            s.passes[2].kernel,
            NttKernelKind::EvalsToMonomialsFinal { stages: 5 }
        ));
        assert_eq!(s.passes.iter().map(|p| p.stage_count).sum::<usize>(), 21);
    }

    #[test]
    fn inverse_columns_per_launch_matches_forward_l2_clamp() {
        // The L2 clamp is direction-independent: pass-1 output is what we want
        // resident across passes. Inverse should hit the same per-`log_n`
        // numbers as forward on an L4-like device (with the 50% L2 budget).
        let l4 = l4_like();
        let cases = [(21, 3), (22, 1), (23, 1), (24, 1)];
        for (log_n, expected) in cases {
            let s = select_ntt_strategy(NttDirection::Inverse, log_n, 4, 1, false, &l4).unwrap();
            assert_eq!(
                s.columns_per_launch, expected,
                "inverse columns_per_launch mismatch at log_n={log_n}",
            );
        }
    }
}
