//! SP2 peek binding: the prover-agnostic `PeekResolver` trait + the independent
//! identity/query-fold oracle. The differential `peek == eval_layer_expr(identity)`
//! is genuine because the peek reads array-mapped values while the oracle recomputes
//! the query arithmetic. See .agents/specs/2026-06-21-gkr-sp2-resolution-binding-design.md §4.

use super::source::{SpecialDescriptor, SpecialStrategy};
use cs::gkr_compiler::dag_ir::{Bf, Ext, LookupResolver, LookupValueKind, RangeWidth, Resolvers};
use field::{Field, PrimeField};
use std::cell::Cell;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PeekError {
    /// A program `Special { desc }` references an out-of-range side-table index.
    DescriptorOutOfRange { desc: u16, table_len: usize },
    /// A referenced descriptor's strategy could not be bound to a real array.
    Unbound { desc: u16 },
    /// A side-table entry no program operand references (and not allow-listed).
    OrphanDescriptor { desc: u16 },
    /// Adapter: a strategy's `set_index` is absent from the real mapping arrays.
    /// (Adapter-produced errors carry no `desc` — the adapter holds the descriptor, not its
    /// table index; the validator owns `desc`-keyed errors.)
    SetIndexOutOfRange { set_index: usize },
    /// `mapping`/`preprocessed_generic_lookup` index out of range.
    IndexOutOfRange { index: usize, len: usize },
    /// `PeekSingleColumn` mapped value exceeds its declared width.
    WidthOverflow { value: u32, width: RangeWidth },
    /// Identity oracle saw `LookupValueKind::DecoderColumn` (not produced by current lowering).
    DecoderColumnUnsupported,
    /// Identity oracle saw an evaluated query with non-base limbs (field/encoding bug).
    NonBaseQueryFold,
    /// `peek(desc,row) != query-fold(origin_expr,row)`. Carries the full spec §7 diagnostic.
    Mismatch { desc: u16, row: usize, strategy: SpecialStrategy, peek: Ext, fold: Ext },
}

/// Returns the base coefficient of `e` iff its three higher limbs are zero.
pub fn base_coeff_pure(e: Ext) -> Option<Bf> {
    use field::FieldExtension;
    let [c0, c1, c2, c3] = <Ext as FieldExtension<Bf>>::into_coeffs(e);
    if c1.is_zero() && c2.is_zero() && c3.is_zero() {
        Some(c0)
    } else {
        None
    }
}

/// The SP2 query-fold oracle's lookup leaf resolver: returns the base coefficient of the
/// already-evaluated query, recording the first invariant violation it sees. Pairing this
/// with the real read/virtual_setup/challenge resolvers turns `eval_layer_expr` into a pure
/// query-fold evaluator (Global Constraints: identity/query-fold, never table-search).
#[derive(Default)]
pub struct IdentityLookupResolver {
    violation: Cell<Option<PeekError>>,
}

impl IdentityLookupResolver {
    pub fn new() -> Self {
        Self { violation: Cell::new(None) }
    }
    /// The first violation recorded during evaluation, if any.
    pub fn took_violation(&self) -> Option<PeekError> {
        self.violation.take_with_clone()
    }
    fn record(&self, e: PeekError) {
        if self.violation.take_with_clone().is_none() {
            self.violation.set(Some(e));
        }
    }
}

// `Cell::take` requires `Default`; `Option<PeekError>: Default`. Helper to peek without
// permanently clearing.
trait TakeWithClone {
    fn take_with_clone(&self) -> Option<PeekError>;
}
impl TakeWithClone for Cell<Option<PeekError>> {
    fn take_with_clone(&self) -> Option<PeekError> {
        let v = self.take();
        self.set(v.clone());
        v
    }
}

impl LookupResolver for IdentityLookupResolver {
    fn lookup(&self, kind: &LookupValueKind, _set_index: usize, evaluated_query: Ext, _row: usize) -> Bf {
        match kind {
            LookupValueKind::DecoderColumn { .. } => {
                self.record(PeekError::DecoderColumnUnsupported);
                Bf::ZERO
            }
            LookupValueKind::RangeCheck16Index
            | LookupValueKind::TimestampIndex
            | LookupValueKind::GenericColumn { .. } => match base_coeff_pure(evaluated_query) {
                Some(c0) => c0,
                None => {
                    self.record(PeekError::NonBaseQueryFold);
                    Bf::ZERO
                }
            },
        }
    }
}

/// Resolves a static `SpecialDescriptor` to its real array-mapped value at `row`.
/// Implemented prover-side (circuit_prover); `gkr_eval_isa` only defines the contract.
pub trait PeekResolver {
    fn peek(&self, desc: &SpecialDescriptor, row: usize, r: &Resolvers<'_>) -> Result<Ext, PeekError>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{Bf, Ext, LookupResolver, LookupValueKind};
    use field::{Field, FieldExtension, PrimeField};

    fn lift(b: Bf) -> Ext { <Ext as FieldExtension<Bf>>::from_base(b) }

    #[test]
    fn base_coeff_pure_accepts_pure_base_rejects_mixed() {
        let pure = lift(Bf::from_u32_with_reduction(7));
        assert_eq!(base_coeff_pure(pure), Some(Bf::from_u32_with_reduction(7)));
        let mixed = Ext::from_array_of_base([
            Bf::from_u32_with_reduction(1), Bf::from_u32_with_reduction(2),
            Bf::ZERO, Bf::ZERO,
        ]);
        assert_eq!(base_coeff_pure(mixed), None);
    }

    #[test]
    fn identity_resolver_returns_query_base_for_generic_and_range_kinds() {
        let id = IdentityLookupResolver::new();
        let q = lift(Bf::from_u32_with_reduction(42));
        assert_eq!(id.lookup(&LookupValueKind::GenericColumn { column: 0 }, 3, q, 0), Bf::from_u32_with_reduction(42));
        assert_eq!(id.lookup(&LookupValueKind::RangeCheck16Index, 0, q, 0), Bf::from_u32_with_reduction(42));
        assert_eq!(id.lookup(&LookupValueKind::TimestampIndex, 0, q, 0), Bf::from_u32_with_reduction(42));
        assert!(id.took_violation().is_none());
    }

    #[test]
    fn identity_resolver_flags_decoder_column() {
        let id = IdentityLookupResolver::new();
        let q = lift(Bf::from_u32_with_reduction(1));
        let _ = id.lookup(&LookupValueKind::DecoderColumn { column: 0 }, 0, q, 0);
        assert_eq!(id.took_violation(), Some(PeekError::DecoderColumnUnsupported));
    }

    #[test]
    fn identity_resolver_flags_non_base_query() {
        let id = IdentityLookupResolver::new();
        let mixed = Ext::from_array_of_base([Bf::ONE, Bf::ONE, Bf::ZERO, Bf::ZERO]);
        let _ = id.lookup(&LookupValueKind::GenericColumn { column: 0 }, 0, mixed, 0);
        assert_eq!(id.took_violation(), Some(PeekError::NonBaseQueryFold));
    }
}
