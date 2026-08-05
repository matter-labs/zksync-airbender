//! SP2 peek binding: the prover-agnostic `PeekResolver` trait + the independent
//! identity/query-fold oracle. The differential `peek == eval_layer_expr(identity)`
//! is genuine because the peek reads array-mapped values while the oracle recomputes
//! the query arithmetic. See .agents/specs/2026-06-21-gkr-sp2-resolution-binding-design.md §4.

use super::source::{SpecialDescriptor, SpecialStrategy};
use field::Field;
use gkr_eval_ir::{Bf, Ext, LookupResolver, LookupValueKind, RangeWidth, Resolvers};
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
    Mismatch {
        desc: u16,
        row: usize,
        strategy: SpecialStrategy,
        peek: Ext,
        fold: Ext,
    },
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
        Self {
            violation: Cell::new(None),
        }
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
    fn lookup(
        &self,
        kind: &LookupValueKind,
        _set_index: usize,
        evaluated_query: Ext,
        _row: usize,
    ) -> Bf {
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
/// Implemented prover-side (circuit_prover); `gpu_gkr_compiler` only defines the contract.
pub trait PeekResolver {
    fn peek(
        &self,
        desc: &SpecialDescriptor,
        row: usize,
        r: &Resolvers<'_>,
    ) -> Result<Ext, PeekError>;
}

// ── SP2: referenced_descriptors + validate_special_bindings ──────────────────

use crate::forward::context::{CompiledLayer, RootOutput};
use crate::forward::isa::{Instr, OperandLine};
use gkr_eval_ir::{DagLayer, eval_layer_expr};
use std::collections::BTreeSet;

/// Every distinct `desc` referenced by an emitted `Special { desc }` operand — from BOTH
/// program instructions AND `RootOutput::Alias` operands. CopyAlias roots emit no bytecode
/// but the interpreter resolves their alias operand after the program, so a `Special{desc}`
/// alias must be covered (F3).
pub fn referenced_descriptors(compiled: &CompiledLayer) -> BTreeSet<u16> {
    let mut out = BTreeSet::new();
    let mut note = |op: &OperandLine| {
        if let OperandLine::Special { desc } = op {
            out.insert(*desc);
        }
    };
    for instr in &compiled.program.instrs {
        for_each_operand(instr, &mut note);
    }
    for (_rid, ro) in &compiled.root_outputs {
        if let RootOutput::Alias(op) = ro {
            note(op);
        }
    }
    out
}

/// Visit every source `OperandLine` of an instruction (the actual `Instr` layout:
/// `Mov.src: Option<OperandLine>`, `Mov.dst: Option<DstLine>` — `DstLine` is never `Special`
/// so destinations are not scanned; `Add`/`Mul` carry `operands: Vec<OperandLine>`;
/// `Fma` carries `pairs: Vec<(OperandLine, OperandLine)>`).
fn for_each_operand(instr: &Instr, f: &mut dyn FnMut(&OperandLine)) {
    match instr {
        Instr::Mov { src, .. } => {
            if let Some(src) = src {
                f(src);
            }
        }
        Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
            for op in operands {
                f(op);
            }
        }
        Instr::Fma { pairs, .. } => {
            for (a, b) in pairs {
                f(a);
                f(b);
            }
        }
    }
}

/// G1 primitive: prove `peek == query-fold` for every referenced descriptor over `rows`,
/// after running the three coverage checks. Returns the comparison count.
pub fn validate_special_bindings(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    rows: &[usize],
    r: &Resolvers<'_>,
    peek: &dyn PeekResolver,
) -> Result<usize, PeekError> {
    let specials = &compiled.ctx.specials;
    let table_len = specials.len();
    let referenced = referenced_descriptors(compiled);

    // Coverage check 1: every reference in range.
    for &desc in &referenced {
        if (desc as usize) >= table_len {
            return Err(PeekError::DescriptorOutOfRange { desc, table_len });
        }
    }
    // Coverage check 3: no orphan side-table entries.
    for desc in 0..table_len as u16 {
        if !referenced.contains(&desc) {
            return Err(PeekError::OrphanDescriptor { desc });
        }
    }

    // Differential: peek vs identity query-fold, every referenced descriptor × every row.
    let mut count = 0usize;
    for &desc in &referenced {
        let d = specials.get(desc).expect("checked in range above");
        for &row in rows {
            let id = IdentityLookupResolver::new();
            let oracle = Resolvers {
                read: r.read,
                lookup: &id,
                virtual_setup: r.virtual_setup,
                challenge: r.challenge,
            };
            let fold = eval_layer_expr(layer, d.origin_expr, row, &oracle);
            if let Some(v) = id.took_violation() {
                return Err(v);
            }
            let peeked = peek.peek(d, row, r)?;
            if peeked != fold {
                return Err(PeekError::Mismatch {
                    desc,
                    row,
                    strategy: d.strategy.clone(),
                    peek: peeked,
                    fold,
                });
            }
            count += 1;
        }
    }
    Ok(count)
}
