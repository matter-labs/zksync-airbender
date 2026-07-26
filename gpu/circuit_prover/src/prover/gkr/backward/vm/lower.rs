//! Host lowering for the backward coefficient-term ISA: bind one round's
//! storage to the compiler's source windows and build the complete by-value
//! [`BwdCoeffDesc`] (design §9.3, §10.2, §11).
//!
//! The compiler has already done everything structural. `bind_coeff_sources`
//! assigned wire windows and window-relative columns, and `encode_program`
//! produced the u16 stream; neither depends on a device pointer. What is left,
//! and all this module does, is:
//!
//!   1. attach the ROUND's physical geometry — read/publish backing, stride,
//!      backing depth, target depth, origin field and the materialize flag — to
//!      each live window;
//!   2. copy the encoded program into the by-value array; and
//!   3. reject anything that would make the launch unsound before it reaches a
//!      release kernel that trusts its descriptor (§12: "release kernels trust
//!      validated artifacts").
//!
//! Source RESOLUTION (Task 10) and the arithmetic loop (Task 11) are device
//! work and are not here. Neither is coefficient-recipe compilation, which
//! Task 13 moves into `backward::coefficients`: this module takes coefficient
//! VALUES already evaluated in the round's challenge context.

// TASK 13 cuts the main-layer prover over to `lower_bwd_coeff`; until then this
// whole module is deliberately unreferenced outside its tests. Scoped here
// rather than on the parent so it does not also cover `report`/`compile`.
#![allow(dead_code)]

use era_cudart::result::CudaResult;
use gkr_eval_isa::bwd::coeff::bind::CoeffSourceBinding;
use gkr_eval_isa::bwd::coeff::encode::EncodedProgram;
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;

use super::desc::{
    BwdCoeffDesc, BwdCoeffSourceWindow, BWD_COEFF_C_INIT_NONE, BWD_COEFF_MAX_BUDGET_CELLS,
    BWD_COEFF_MAX_COEFFICIENT_ENCODINGS, BWD_COEFF_MAX_FOLD_DEPTH, BWD_COEFF_MIN_BUDGET_CELLS,
    BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT,
    BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE, BWD_COEFF_PROGRAM_WORD_CAP,
    BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_COEFF_SOURCE_WINDOW_CAP, BWD_COEFF_SOURCE_WINDOW_COLUMNS,
};
use super::{bwd_coeff_fold_depth, BwdCoeffBank};
use crate::primitives::field::E4;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::prover::ProverContext;
use crate::upstream::{BwdRegime, Field};

/// Bytes one column of a backing occupies, by storage field.
const BF_COLUMN_BYTES: u32 = 4;
const E4_COLUMN_BYTES: u32 = 16;

// ── Round binding inputs ─────────────────────────────────────────────────────

/// The round's physical geometry for ONE bound source window.
///
/// Indexed positionally by wire window: entry `w` describes
/// `CoeffSourceBinding::windows[w]`. `read`/`publish` name the window's FIRST
/// column, so the device resolves a bound coordinate as
/// `read_base + column * read_stride_bytes`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedBwdCoeffSourceWindow {
    /// The matrix column the window is based at. `None` only for a procedural
    /// window whose values are produced from the row rather than read.
    pub read: Option<ResolvedColumn>,
    /// Where a first access publishes both raw target-depth endpoints. Required
    /// whenever `materialize` is set.
    pub publish: Option<ResolvedColumn>,
    /// Depth the read backing is currently at.
    pub backing_depth: u8,
    /// Depth a use of this window must observe.
    pub target_depth: u8,
    /// §10.2's static policy: publish on first physical access. Layer-wide, but
    /// carried per entry so the device never has to consult two places.
    pub materialize: bool,
}

/// Everything about one sumcheck round that is not in the compiled program.
pub(crate) struct BwdCoeffRoundBinding<'a> {
    /// Sumcheck round index. It is ALSO the fold prelude's target depth and the
    /// number of active round challenges — `lower_bwd_coeff` enforces
    /// `n_round_challenges == round` so those three cannot diverge.
    pub round: u8,
    /// Logical rows this launch evaluates — one per thread, and the
    /// contribution half-stride.
    pub rows: u32,
    /// Device-resident transcript challenges for the lazy-fold prelude. Must be
    /// non-null whenever `n_round_challenges > 0`.
    pub round_challenges: *const E4,
    pub n_round_challenges: u32,
    /// One entry per `CoeffSourceBinding::windows` entry, in wire order.
    pub windows: &'a [ResolvedBwdCoeffSourceWindow],
    pub eq_low: *const E4,
    pub eq_sizes: GkrEqSizes,
    pub contributions: *mut E4,
}

/// A lowered launch: the by-value descriptor plus the coefficient bank it was
/// lowered against.
pub(crate) struct BwdCoeffSetup {
    pub desc: BwdCoeffDesc,
    /// Bank entries, in index order. Coefficient index `i >= RESERVED` names
    /// `coefficients[i - RESERVED]`; `+1` and `-1` never reach the bank.
    pub coefficients: Vec<E4>,
    pub bank: BwdCoeffBank,
    pub regime: BwdRegime,
    pub fold_depth: u8,
}

impl BwdCoeffSetup {
    /// Stage the constant-backed coefficient bank.
    ///
    /// A no-op for [`BwdCoeffBank::DevicePointer`], whose values are already
    /// device-resident behind `desc.coefficients`. The copy is enqueued on
    /// `exec_stream`, so a following launch observes it with no host
    /// synchronization; unused slots are cleared to keep relaunches independent
    /// of the previous setup.
    pub(crate) fn upload_constant_bank(&self, context: &ProverContext) -> CudaResult<()> {
        if self.bank != BwdCoeffBank::Constant {
            return Ok(());
        }
        assert_eq!(self.coefficients.len(), self.desc.n_coefficients as usize);
        assert!(self.coefficients.len() <= FLAT_CONST_MAX);
        let bank: [E4; FLAT_CONST_MAX] =
            core::array::from_fn(|index| self.coefficients.get(index).copied().unwrap_or(E4::ZERO));
        // SAFETY: the Rust static is the stub for the exact CUDA `__constant__`
        // E4 array with a matching element count and layout. The pageable
        // source is staged by `cudaMemcpyToSymbolAsync` before this returns,
        // and the device copy stays ordered before the caller's next
        // exec-stream launch.
        unsafe {
            crate::primitives::utils::memcpy_to_symbol_async(
                &super::ab_gkr_flat_coefficients,
                &bank,
                context.get_exec_stream(),
            )
        }
    }
}

// ── Errors ───────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BwdCoeffLowerError {
    /// The encoded stream does not fit the by-value program array. §9.1: this
    /// requires a tighter encoding or a re-measured pin, never a device program
    /// pointer.
    ProgramOverflow { words: usize, cap: usize },
    /// More live windows than the measured corpus maximum the descriptor is
    /// sized from.
    SourceWindowOverflow { windows: usize, cap: usize },
    /// The round supplied a different number of window bindings than the
    /// compiled program has windows.
    SourceWindowCountMismatch { compiled: usize, bound: usize },
    /// A matrix-backed window has no read backing.
    MissingReadBacking { window: u8 },
    /// A window's read or publish backing is null, or its stride is zero.
    NullWindowGeometry { window: u8 },
    /// A backing's column stride does not match its storage field.
    WindowStrideMismatch {
        window: u8,
        is_e4: bool,
        stride_bytes: u32,
    },
    /// A materializing window has no publish backing.
    MissingPublishBacking { window: u8 },
    /// A non-materializing window was given a publish backing.
    UnexpectedPublishBacking { window: u8 },
    /// A procedural window addresses more than one column.
    ///
    /// A procedural value is produced from the backing INDEX, so the device
    /// resolver has nothing to do with the column coordinate and ignores it. One
    /// virtual-setup kind is one column, and each kind is its own
    /// `WindowFamily::VirtualSetup { kind }`, so a multi-column procedural window
    /// cannot arise from binding — but if one ever did, every column past the
    /// first would silently resolve to column zero's values.
    MultiColumnProceduralWindow { window: u8, columns: usize },
    /// A procedural window named a kind outside `KIND_ORDER`.
    UnknownProceduralKind { window: u8, kind: u8 },
    /// A window addresses more than the 128 columns its `column:7` coordinate
    /// can reach.
    WindowColumnOverflow { window: u8, offset: usize },
    /// `backing_depth > target_depth`, or a depth outside the bounded D0..D3
    /// resolver range.
    InvalidDepths {
        window: u8,
        backing_depth: u8,
        target_depth: u8,
    },
    /// The materialize flag disagrees with §10.2's static depth policy.
    MaterializationPolicyMismatch {
        window: u8,
        target_depth: u8,
        materialize: bool,
    },
    /// A window's target depth is not the layer-wide one the program was bound
    /// for.
    TargetDepthMismatch {
        window: u8,
        expected: u8,
        actual: u8,
    },
    /// The compiled program's layer-wide target depth is not this round.
    ///
    /// The fold prelude builds its weights from `round` (it is handed
    /// `n_round_challenges` as its target depth), while the device resolves a
    /// window's catch-up from `target_depth - backing_depth`. The two only name
    /// the same challenges when the layer's target depth IS the round, so a
    /// mismatch would weight a correct-looking fold with the wrong challenges —
    /// silently, in a release kernel with no error channel.
    RoundTargetDepthMismatch { round: u8, target_depth: u8 },
    /// An R0 program was lowered for a round other than zero.
    ///
    /// `launch_bwd_coeff` matches `(BwdRegime::R0, _, bank)` and always launches
    /// the `<REGIME_IS_R0 = true, FOLD_DEPTH = 0>` specialization, because R0 IS
    /// round zero. Nothing else in this function notices: an R0 program at round
    /// three passes the challenge-count and target-depth checks and then runs a
    /// kernel whose BF resolver never folds and whose E4 resolver accumulates
    /// leaf zero only. Silently wrong, in a kernel with no error channel.
    R0RoundMismatch { round: u8 },
    /// A window's catch-up distance is not one the runtime factor bank can
    /// weight.
    ///
    /// `ab_gkr_bwd_coeff_build_fold_factors_kernel` fills exactly two groups:
    /// the depth-one pair and one depth-`fold_depth` leaf table (§10.2). So a
    /// window is either already at target depth, one fold behind, or has never
    /// caught up — nothing between.
    UnsupportedFoldDelta {
        window: u8,
        delta: u8,
        fold_depth: u8,
    },
    /// A publish range overlaps a read range or another publish range.
    UnsafePublishAlias { window: u8, other: u8 },
    /// The cell budget is outside c2..c16.
    InvalidCellBudget { cells: u32 },
    /// `c_init` names a coefficient index the bank cannot supply.
    InvalidCInit { index: u32 },
    /// More coefficients than the selected bank holds.
    CoefficientBankOverflow { coefficients: usize, cap: usize },
    /// The device-pointer bank has entries but no pointer.
    MissingCoefficientPointer,
    /// `n_round_challenges` is not exactly the round index.
    ///
    /// They are one number wearing two hats: `n_round_challenges` is what the
    /// launcher hands the fold prelude as its `target_depth`, and `round` is
    /// what selects the D0..D3 resolver. `>=` would let the prelude build
    /// weights for a different depth than the kernel decodes at, silently, so
    /// the relation is equality.
    RoundChallengeCountMismatch { round: u8, n_round_challenges: u32 },
    /// A runtime pointer the kernel dereferences unconditionally is null.
    NullRuntimePointer { what: &'static str },
}

// ── Lowering ─────────────────────────────────────────────────────────────────

/// Build the complete by-value descriptor for one `(program, round)` pair.
///
/// `coefficients` are already evaluated in this round's challenge context and
/// indexed as bank entries: coefficient index `i` names `coefficients[i -
/// RESERVED]`, and the reserved `+1` / `-1` indices never reach the bank.
pub(crate) fn lower_bwd_coeff(
    program: &EncodedProgram,
    binding: &CoeffSourceBinding,
    runtime: &BwdCoeffRoundBinding<'_>,
    coefficients: Vec<E4>,
    coefficient_ptr: *const E4,
    bank: BwdCoeffBank,
) -> Result<BwdCoeffSetup, BwdCoeffLowerError> {
    if program.words.len() > BWD_COEFF_PROGRAM_WORD_CAP {
        return Err(BwdCoeffLowerError::ProgramOverflow {
            words: program.words.len(),
            cap: BWD_COEFF_PROGRAM_WORD_CAP,
        });
    }
    if binding.windows.len() > BWD_COEFF_SOURCE_WINDOW_CAP {
        return Err(BwdCoeffLowerError::SourceWindowOverflow {
            windows: binding.windows.len(),
            cap: BWD_COEFF_SOURCE_WINDOW_CAP,
        });
    }
    if binding.windows.len() != runtime.windows.len() {
        return Err(BwdCoeffLowerError::SourceWindowCountMismatch {
            compiled: binding.windows.len(),
            bound: runtime.windows.len(),
        });
    }

    let cells = u32::from(program.budget.cells());
    if !(BWD_COEFF_MIN_BUDGET_CELLS..=BWD_COEFF_MAX_BUDGET_CELLS).contains(&cells) {
        return Err(BwdCoeffLowerError::InvalidCellBudget { cells });
    }

    let cap = bank.capacity();
    if coefficients.len() > cap {
        return Err(BwdCoeffLowerError::CoefficientBankOverflow {
            coefficients: coefficients.len(),
            cap,
        });
    }
    if bank == BwdCoeffBank::DevicePointer && !coefficients.is_empty() && coefficient_ptr.is_null()
    {
        return Err(BwdCoeffLowerError::MissingCoefficientPointer);
    }

    let c_init = lower_c_init(program, coefficients.len())?;
    let fold_depth = bwd_coeff_fold_depth(runtime.round);
    // `launch_fold_factor_prelude` passes `desc.n_round_challenges` as the
    // prelude's `target_depth` while `fold_depth` comes from `round`. Equality
    // is what keeps those two readings of one number from diverging.
    if runtime.n_round_challenges != u32::from(runtime.round) {
        return Err(BwdCoeffLowerError::RoundChallengeCountMismatch {
            round: runtime.round,
            n_round_challenges: runtime.n_round_challenges,
        });
    }
    // ...and the program's own target depth has to be that same round, or the
    // prelude's weights belong to a different fold than the device performs.
    if binding.target_depth != runtime.round {
        return Err(BwdCoeffLowerError::RoundTargetDepthMismatch {
            round: runtime.round,
            target_depth: binding.target_depth,
        });
    }
    // ...and R0 IS round zero. `launch_bwd_coeff` ignores the fold depth for the
    // R0 arm and always launches the D0 specialization, so an R0 program lowered
    // for a later round would run a kernel that cannot fold.
    if program.regime == BwdRegime::R0 && runtime.round != 0 {
        return Err(BwdCoeffLowerError::R0RoundMismatch {
            round: runtime.round,
        });
    }
    // A release kernel has no error channel, so the host is the only place a
    // null it would dereference can be reported. The device keeps its own guard
    // as defence in depth against a hand-built descriptor.
    if runtime.contributions.is_null() {
        return Err(BwdCoeffLowerError::NullRuntimePointer {
            what: "contributions",
        });
    }
    if runtime.eq_low.is_null() {
        return Err(BwdCoeffLowerError::NullRuntimePointer { what: "eq_low" });
    }
    if runtime.n_round_challenges > 0 && runtime.round_challenges.is_null() {
        return Err(BwdCoeffLowerError::NullRuntimePointer {
            what: "round_challenges",
        });
    }

    let mut desc = BwdCoeffDesc::empty();
    let mut window_columns = Vec::with_capacity(binding.windows.len());
    for (index, (compiled, bound)) in binding.windows.iter().zip(runtime.windows).enumerate() {
        let window = index as u8;
        let procedural_kind = match compiled.family {
            WindowFamily::VirtualSetup { kind } => {
                if usize::from(kind) >= BWD_COEFF_PROCEDURAL_KINDS {
                    return Err(BwdCoeffLowerError::UnknownProceduralKind { window, kind });
                }
                Some(kind)
            }
            _ => None,
        };
        let widest = compiled
            .columns
            .last()
            .map(|column| column.column - compiled.first_column)
            .unwrap_or(0);
        if widest >= BWD_COEFF_SOURCE_WINDOW_COLUMNS {
            return Err(BwdCoeffLowerError::WindowColumnOverflow {
                window,
                offset: widest,
            });
        }
        let columns = widest + 1;
        window_columns.push(columns);
        desc.source_windows[index] = lower_window(
            window,
            procedural_kind,
            columns,
            binding.target_depth,
            fold_depth,
            bound,
        )?;
    }
    check_publish_aliases(
        &desc.source_windows[..binding.windows.len()],
        &window_columns,
    )?;

    desc.coefficients = if bank == BwdCoeffBank::DevicePointer {
        coefficient_ptr
    } else {
        std::ptr::null()
    };
    desc.round_challenges = runtime.round_challenges;
    desc.eq_low = runtime.eq_low;
    desc.contributions = runtime.contributions;
    desc.eq_sizes = runtime.eq_sizes;
    desc.num_words = program.words.len() as u32;
    desc.n_source_windows = binding.windows.len() as u32;
    desc.n_round_challenges = runtime.n_round_challenges;
    desc.n_coefficients = coefficients.len() as u32;
    desc.logical_rows = runtime.rows;
    desc.cell_budget = cells;
    desc.c_init = c_init;
    desc.program[..program.words.len()].copy_from_slice(&program.words);

    Ok(BwdCoeffSetup {
        desc,
        coefficients,
        bank,
        regime: program.regime,
        fold_depth,
    })
}

/// `c_init` as a descriptor coefficient index, or the absent sentinel.
///
/// The sentinel is `u16::MAX`, which is NOT reachable as a coefficient encoding
/// — thirteen coefficient bits top out well below it — so a reader can never
/// mistake one for the other.
fn lower_c_init(program: &EncodedProgram, bank_entries: usize) -> Result<u16, BwdCoeffLowerError> {
    let Some(recipe) = program.c_init else {
        return Ok(BWD_COEFF_C_INIT_NONE);
    };
    let index = recipe.0;
    let in_bank = match recipe.bank_index() {
        Some(slot) => slot < bank_entries,
        // The reserved `+1` / `-1` literals never touch the bank.
        None => true,
    };
    if !in_bank || index as usize >= BWD_COEFF_MAX_COEFFICIENT_ENCODINGS {
        return Err(BwdCoeffLowerError::InvalidCInit { index });
    }
    Ok(index as u16)
}

fn lower_window(
    window: u8,
    procedural_kind: Option<u8>,
    columns: usize,
    layer_target_depth: u8,
    fold_depth: u8,
    bound: &ResolvedBwdCoeffSourceWindow,
) -> Result<BwdCoeffSourceWindow, BwdCoeffLowerError> {
    if bound.target_depth != layer_target_depth {
        return Err(BwdCoeffLowerError::TargetDepthMismatch {
            window,
            expected: layer_target_depth,
            actual: bound.target_depth,
        });
    }
    if bound.backing_depth > bound.target_depth
        || bound.target_depth - bound.backing_depth > BWD_COEFF_MAX_FOLD_DEPTH
    {
        return Err(BwdCoeffLowerError::InvalidDepths {
            window,
            backing_depth: bound.backing_depth,
            target_depth: bound.target_depth,
        });
    }
    // The device's bounded lazy resolver indexes the runtime factor bank by
    // catch-up distance, and the bank holds only the depth-one pair and one
    // depth-`fold_depth` table.
    let delta = bound.target_depth - bound.backing_depth;
    if delta > fold_depth || !(delta == 0 || delta == 1 || delta == fold_depth) {
        return Err(BwdCoeffLowerError::UnsupportedFoldDelta {
            window,
            delta,
            fold_depth,
        });
    }
    // §10.2's materialization policy is static, not a per-window choice.
    if bound.materialize != (bound.target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH) {
        return Err(BwdCoeffLowerError::MaterializationPolicyMismatch {
            window,
            target_depth: bound.target_depth,
            materialize: bound.materialize,
        });
    }
    if bound.materialize && bound.publish.is_none() {
        return Err(BwdCoeffLowerError::MissingPublishBacking { window });
    }
    if !bound.materialize && bound.publish.is_some() {
        return Err(BwdCoeffLowerError::UnexpectedPublishBacking { window });
    }

    // A procedural window's values come from the backing index, so the device
    // resolver has no use for the column coordinate. Reject the case where that
    // would matter rather than silently resolve every column to the first.
    if procedural_kind.is_some() && columns > 1 {
        return Err(BwdCoeffLowerError::MultiColumnProceduralWindow { window, columns });
    }

    let origin = match (procedural_kind, bound.read) {
        (Some(_), _) => BWD_COEFF_ORIGIN_PROCEDURAL,
        (None, Some(read)) if read.is_e4 => BWD_COEFF_ORIGIN_READ_EXT,
        (None, Some(_)) => BWD_COEFF_ORIGIN_READ_BASE,
        (None, None) => return Err(BwdCoeffLowerError::MissingReadBacking { window }),
    };

    let (read_base, read_stride_bytes) = match bound.read {
        Some(read) => {
            check_column_geometry(window, &read)?;
            (read.ptr, read.stride_bytes)
        }
        None => (std::ptr::null(), 0),
    };
    let (publish_base, publish_stride_bytes) = match bound.publish {
        Some(publish) => {
            check_column_geometry(window, &publish)?;
            (publish.ptr as *mut u8, publish.stride_bytes)
        }
        None => (std::ptr::null_mut(), 0),
    };
    // A window addresses `columns` contiguous columns of each backing; the far
    // end must still be a representable address.
    for (base, stride) in [
        (read_base as usize, read_stride_bytes),
        (publish_base as usize, publish_stride_bytes),
    ] {
        if base != 0 && base.checked_add(columns * stride as usize).is_none() {
            return Err(BwdCoeffLowerError::NullWindowGeometry { window });
        }
    }

    Ok(BwdCoeffSourceWindow {
        read_base,
        publish_base,
        read_stride_bytes,
        publish_stride_bytes,
        backing_depth: bound.backing_depth,
        target_depth: bound.target_depth,
        origin,
        materialize: u8::from(bound.materialize),
        procedural_kind: procedural_kind.unwrap_or(BWD_COEFF_PROCEDURAL_NONE),
        reserved: [0; 3],
    })
}

fn check_column_geometry(window: u8, column: &ResolvedColumn) -> Result<(), BwdCoeffLowerError> {
    if column.ptr.is_null() || column.stride_bytes == 0 {
        return Err(BwdCoeffLowerError::NullWindowGeometry { window });
    }
    let element = if column.is_e4 {
        E4_COLUMN_BYTES
    } else {
        BF_COLUMN_BYTES
    };
    if column.stride_bytes % element != 0 {
        return Err(BwdCoeffLowerError::WindowStrideMismatch {
            window,
            is_e4: column.is_e4,
            stride_bytes: column.stride_bytes,
        });
    }
    Ok(())
}

/// A published range may not overlap any read range or any other published
/// range: a first access writes both raw target-depth endpoints, and a write
/// racing a read of the same bytes is a correctness bug the kernel cannot see.
///
/// `columns[w]` is window `w`'s ACTUAL addressable column count, not the 128 the
/// coordinate can reach — two windows of one backing may be based fewer than 128
/// columns apart, so the encoding limit would report a phantom overlap.
fn check_publish_aliases(
    windows: &[BwdCoeffSourceWindow],
    columns: &[usize],
) -> Result<(), BwdCoeffLowerError> {
    debug_assert_eq!(windows.len(), columns.len());
    let span = |base: *const u8, stride: u32, count: usize| -> Option<(usize, usize)> {
        (!base.is_null()).then(|| (base as usize, base as usize + count * stride as usize))
    };
    for (index, window) in windows.iter().enumerate() {
        let Some((publish_lo, publish_hi)) = span(
            window.publish_base as *const u8,
            window.publish_stride_bytes,
            columns[index],
        ) else {
            continue;
        };
        for (other_index, other) in windows.iter().enumerate() {
            let mut ranges = Vec::with_capacity(2);
            ranges.extend(span(
                other.read_base,
                other.read_stride_bytes,
                columns[other_index],
            ));
            if other_index != index {
                ranges.extend(span(
                    other.publish_base as *const u8,
                    other.publish_stride_bytes,
                    columns[other_index],
                ));
            }
            for (lo, hi) in ranges {
                if publish_lo < hi && lo < publish_hi {
                    return Err(BwdCoeffLowerError::UnsafePublishAlias {
                        window: index as u8,
                        other: other_index as u8,
                    });
                }
            }
        }
    }
    Ok(())
}
