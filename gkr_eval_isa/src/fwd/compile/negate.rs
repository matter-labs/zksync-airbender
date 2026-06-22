//! Negate canonicalization, sign-vs-negate cost model, and strength invariants (spec §6).
//!
//! `canonicalize_product` splits any `Special(NegOne)` factor out of a product,
//! reducing it to a parity-flipped negate flag + the remaining factors. A `MUL`
//! carrying `-1` among other factors is never emitted downstream.
//!
//! Note (#7): when a negated term is an ADDEND of a sum, the negate is folded into
//! the consuming ADD/FMA as a `Sign::Minus` bit — zero extra instructions — by
//! `arith.rs::classify_additive_child`, which peels the `-1` parity at the `ExprId`
//! level (via `mul_surviving_factors`). That path does NOT
//! go through this module's `OperandLine`-level helpers below.
//!
//! `choose_sign_vs_negate` selects the cheaper strategy for a homogeneous negative
//! group: either per-term sign bits (`PerTermSign`) or a single post-ADD negate
//! (`AddThenNegate`). Costs are tunable (measured in SP3).
//!
//! `assert_no_zero_operand` enforces the strength invariant that `Special(Zero)`
//! never appears as an arithmetic operand.
//!
//! # SP1 wiring status
//!
//! **None of the public items in this module are called by the SP1 compile path.**
//! `compile_mul` (in `mul.rs`) strips `-1` factors at the `ExprId` level before
//! reaching the instruction-emission stage, so `canonicalize_product` is not
//! invoked there. Likewise, the sign-vs-negate cost decision (`choose_sign_vs_negate`,
//! `Costs`, `Strategy`) and the zero-operand strength guard (`assert_no_zero_operand`)
//! are retained, unit-tested, and targeted for **SP3 wiring and on-device
//! measurement** — they are intentional forward work, not accidentally-dead code.

use super::super::error::CompileError;
use super::super::isa::{LdcSub, OperandLine, Special};

// ── canonicalize_product ──────────────────────────────────────────────────────

/// Strip any `Special(NegOne)` factors from `factors`, returning a sign parity
/// and the remaining factors (free of `-1` entries).
///
/// - An **odd** count of `-1` factors → `(true, rest)`.
/// - An **even** count of `-1` factors → `(false, rest)`.
/// - No `-1` factors → `(false, factors.to_vec())`.
///
/// A `MUL` carrying `-1` among other factors must never be emitted; the caller
/// emits the remaining MUL then, if `negate == true`, a unary `MUL Special(NegOne)`
/// (spec §6 negate = unary negation, not a mixed multiply).
pub fn canonicalize_product(factors: &[OperandLine]) -> (bool, Vec<OperandLine>) {
    let neg_one_count = factors
        .iter()
        .filter(|&&op| is_neg_one(op))
        .count();
    let negate = neg_one_count % 2 == 1;
    let rest: Vec<OperandLine> = factors
        .iter()
        .copied()
        .filter(|&op| !is_neg_one(op))
        .collect();
    (negate, rest)
}

fn is_neg_one(op: OperandLine) -> bool {
    matches!(
        op,
        OperandLine::Ldc {
            sub: LdcSub::Special,
            idx,
        } if idx == Special::NegOne as u16
    )
}

// ── choose_sign_vs_negate ─────────────────────────────────────────────────────

/// Cost parameters for the sign-vs-negate decision (spec §6, §11).
///
/// All costs are in abstract "work units" (measured on-device in SP3; tunable).
/// Defaults are notional; they are overridden by real measurements before SP3.
pub struct Costs {
    /// Cost of one additive accumulation with a `+` sign (ADD+).
    pub add: u32,
    /// Cost of one additive accumulation with a `−` sign (ADD−).
    pub sub: u32,
    /// Cost of a single field negate (`MUL Special(NegOne)`, unary).
    pub negate: u32,
}

/// Strategy for handling a homogeneous negative term group (spec §6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    /// Emit all terms with `+` sign, then apply one unary negate at the end.
    /// Cheaper when `n * (sub_cost − add_cost) > negate_cost`.
    AddThenNegate,
    /// Emit each term with its natural `−` sign bit.
    PerTermSign,
}

/// Select between emitting per-term sign bits vs. a single post-sum negate,
/// given `n` terms in the negative group.
///
/// Decision rule (spec §6):
/// `AddThenNegate` when `n * (sub − add) > negate`, else `PerTermSign`.
///
/// When `sub <= add` the rule always selects `PerTermSign` (sub is no more
/// expensive than add, so the sign flag is never a cost).
pub fn choose_sign_vs_negate(n: usize, costs: &Costs) -> Strategy {
    let savings_per_term = costs.sub.saturating_sub(costs.add);
    let total_savings = (n as u64) * (savings_per_term as u64);
    if total_savings > costs.negate as u64 {
        Strategy::AddThenNegate
    } else {
        Strategy::PerTermSign
    }
}

// ── assert_no_zero_operand ────────────────────────────────────────────────────

/// Reject any operand list that contains `Special(Zero)`.
///
/// `0` must never appear as an arithmetic operand (spec §6 strength invariants):
/// `ADD 0` is a NOP and must be dropped; multiplying by `0` is never emitted.
pub fn assert_no_zero_operand(operands: &[OperandLine]) -> Result<(), CompileError> {
    for &op in operands {
        if is_zero(op) {
            return Err(CompileError::FieldMismatch(
                "strength violation: Special(Zero) used as arithmetic operand".into(),
            ));
        }
    }
    Ok(())
}

fn is_zero(op: OperandLine) -> bool {
    matches!(
        op,
        OperandLine::Ldc {
            sub: LdcSub::Special,
            idx,
        } if idx == Special::Zero as u16
    )
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::super::isa::{LdcSub, OperandLine, Special};
    fn neg_one() -> OperandLine { OperandLine::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 } }
    fn zero() -> OperandLine { OperandLine::Ldc { sub: LdcSub::Special, idx: Special::Zero as u16 } }
    #[test]
    fn product_with_neg_one_splits() {
        let (neg, rest) = canonicalize_product(&[OperandLine::Smem { cell: 0 }, neg_one(), OperandLine::Smem { cell: 4 }]);
        assert!(neg);
        assert_eq!(rest, vec![OperandLine::Smem { cell: 0 }, OperandLine::Smem { cell: 4 }]);
    }
    #[test]
    fn sign_vs_negate_picks_by_cost() {
        let costs = Costs { add: 1, sub: 3, negate: 4 };
        assert_eq!(choose_sign_vs_negate(10, &costs), Strategy::AddThenNegate); // 10*2 > 4
        assert_eq!(choose_sign_vs_negate(1, &costs), Strategy::PerTermSign);    // 1*2 < 4
    }
    #[test]
    fn zero_operand_rejected() { assert!(assert_no_zero_operand(&[zero()]).is_err()); }
}
