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

// ── SP2: referenced_descriptors + validate_special_bindings ──────────────────

use crate::fwd::context::{CompiledLayer, RootOutput};
use crate::fwd::isa::{Instr, OperandLine, Program};
use cs::gkr_compiler::dag_ir::{eval_layer_expr, DagLayer};
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
        Instr::Mov { src, .. } => { if let Some(src) = src { f(src); } }
        Instr::Add { operands, .. } | Instr::Mul { operands, .. } => { for op in operands { f(op); } }
        Instr::Fma { pairs, .. } => { for (a, b) in pairs { f(a); f(b); } }
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
                return Err(PeekError::Mismatch { desc, row, strategy: d.strategy.clone(), peek: peeked, fold });
            }
            count += 1;
        }
    }
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::{referenced_descriptors, validate_special_bindings};
    use crate::fwd::context::CompiledLayer;
    use crate::fwd::isa::{Instr, OperandLine, Program};
    use crate::fwd::source::{SpecialDescriptor, SpecialStrategy};
    use cs::gkr_compiler::dag_ir::{Bf, Ext, ExprId, LookupResolver, LookupValueKind, RangeWidth};
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

    // ── SP2 tests: referenced_descriptors + validate_special_bindings ─────────

    // A PeekResolver stub that returns a fixed value, to drive the differential logic.
    struct StubPeek(Ext);
    impl PeekResolver for StubPeek {
        fn peek(&self, _d: &SpecialDescriptor, _row: usize, _r: &Resolvers<'_>) -> Result<Ext, PeekError> {
            Ok(self.0)
        }
    }

    // ── Test helpers ──────────────────────────────────────────────────────────

    use crate::fwd::binding::{BackingKey, BackingTable};
    use crate::fwd::context::{CompileTrace, DagForwardContext, OutputCell, RootOutput};
    use crate::fwd::stats::CompileStats;
    use crate::fwd::source::{ConstBank, SpecialTable};
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ChallengeRef, DagLayer, ReadPlace, Resolvers, RootId,
        SinkId, SinkKind, SourceKind, VirtualSetupKind,
    };
    use std::collections::BTreeMap;

    struct ZeroReadResolver;
    impl cs::gkr_compiler::dag_ir::ReadResolver for ZeroReadResolver {
        fn read(&self, _place: &ReadPlace, _row: usize) -> Ext { Ext::ZERO }
    }
    struct ZeroLookupResolverSp2;
    impl cs::gkr_compiler::dag_ir::LookupResolver for ZeroLookupResolverSp2 {
        fn lookup(&self, _kind: &LookupValueKind, _set_index: usize, _evaluated_query: Ext, _row: usize) -> Bf { Bf::ZERO }
    }
    struct ZeroVirtualSetupResolver;
    impl cs::gkr_compiler::dag_ir::VirtualSetupResolver for ZeroVirtualSetupResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, _row: usize) -> Bf { Bf::ZERO }
    }
    struct ZeroChallengeResolver;
    impl cs::gkr_compiler::dag_ir::ChallengeResolver for ZeroChallengeResolver {
        fn challenge(&self, _r: &ChallengeRef) -> Ext { Ext::ZERO }
    }

    fn make_resolvers_sp2<'a>(
        read: &'a dyn cs::gkr_compiler::dag_ir::ReadResolver,
        lookup: &'a dyn cs::gkr_compiler::dag_ir::LookupResolver,
        challenge: &'a dyn cs::gkr_compiler::dag_ir::ChallengeResolver,
    ) -> Resolvers<'a> {
        Resolvers {
            read,
            lookup,
            virtual_setup: &ZeroVirtualSetupResolver,
            challenge,
        }
    }

    fn empty_dag_layer() -> DagLayer {
        DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            sinks: vec![],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        }
    }

    fn minimal_compiled_with_specials(
        program: Program,
        root_outputs: Vec<(RootId, RootOutput)>,
        specials: SpecialTable,
    ) -> CompiledLayer {
        let mut backings = BackingTable::default();
        backings.intern(BackingKey::BaseLayerMemory).unwrap();
        let ctx = DagForwardContext {
            specials,
            consts: ConstBank::default(),
            challenges: crate::fwd::source::ChallengeBanks::default(),
            backings,
            actions: std::collections::HashMap::new(),
            cache_loc: std::collections::HashMap::new(),
            cross_layer_fields: std::collections::HashMap::new(),
        };
        CompiledLayer {
            program,
            ctx,
            root_outputs,
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 4,
            stats: CompileStats::default(),
        }
    }

    /// Build a CompiledLayer with one descriptor in the side-table and one instruction
    /// referencing Special { desc } in an Add operand.
    fn compiled_with_one_descriptor_and_reference(desc: u16) -> CompiledLayer {
        let mut specials = SpecialTable::default();
        specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: ExprId(0),
        });
        let program = Program {
            instrs: vec![Instr::Add {
                field: crate::fwd::isa::OperandField::Base,
                sign: crate::fwd::isa::Sign::Plus,
                operands: vec![OperandLine::Special { desc }],
            }],
        };
        minimal_compiled_with_specials(program, vec![], specials)
    }

    /// Build a CompiledLayer with two descriptors but only the first referenced by the program.
    fn compiled_with_two_descriptors_one_referenced() -> CompiledLayer {
        let mut specials = SpecialTable::default();
        specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: ExprId(0),
        });
        specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: ExprId(0),
        });
        let program = Program {
            instrs: vec![Instr::Add {
                field: crate::fwd::isa::OperandField::Base,
                sign: crate::fwd::isa::Sign::Plus,
                operands: vec![OperandLine::Special { desc: 0 }],
            }],
        };
        minimal_compiled_with_specials(program, vec![], specials)
    }

    /// Build a CompiledLayer with empty program.instrs and one RootOutput::Alias(Special { desc: 0 }).
    fn compiled_with_alias_special_desc0_no_program_ref() -> CompiledLayer {
        let mut specials = SpecialTable::default();
        specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: ExprId(0),
        });
        let program = Program { instrs: vec![] };
        let root_outputs = vec![(RootId(0), RootOutput::Alias(OperandLine::Special { desc: 0 }))];
        minimal_compiled_with_specials(program, root_outputs, specials)
    }

    /// Build a CompiledLayer with one descriptor whose origin_expr is a DAG Constant(v),
    /// and one instruction referencing desc 0. Returns (CompiledLayer, DagLayer with constant expr).
    fn compiled_peek_setup_desc0_origin_const(v: u32) -> CompiledLayer {
        let mut arena = ArenaBuilder::new();
        let const_src = arena.intern_source(SourceKind::Constant { value: v });
        let const_expr = arena.source_expr(const_src);

        let mut specials = SpecialTable::default();
        specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: const_expr,
        });
        let program = Program {
            instrs: vec![Instr::Add {
                field: crate::fwd::isa::OperandField::Base,
                sign: crate::fwd::isa::Sign::Plus,
                operands: vec![OperandLine::Special { desc: 0 }],
            }],
        };
        // We need to also return the layer, but the test function only returns CompiledLayer.
        // Store the const_expr as ExprId(0) — ArenaBuilder always produces ExprId(0) for first expr.
        // The stub_layer_resolvers_rows will build a matching layer.
        minimal_compiled_with_specials(program, vec![], specials)
    }

    /// Returns (layer, resolvers, rows) for the const-fold tests.
    /// The layer contains a single Constant source at ExprId(0).
    fn stub_layer_resolvers_rows<'a>() -> (DagLayer, (impl cs::gkr_compiler::dag_ir::ReadResolver, impl cs::gkr_compiler::dag_ir::LookupResolver, impl cs::gkr_compiler::dag_ir::ChallengeResolver), Vec<usize>) {
        // Build a DagLayer with one Constant(7) source so ExprId(0) = Constant(7).
        // NOTE: This ExprId matches what compiled_peek_setup_desc0_origin_const stores.
        let mut arena = ArenaBuilder::new();
        let const_src = arena.intern_source(SourceKind::Constant { value: 7 });
        let _const_expr = arena.source_expr(const_src);
        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![],
            sinks: vec![],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        let rows = vec![0usize];
        (layer, (ZeroReadResolver, ZeroLookupResolverSp2, ZeroChallengeResolver), rows)
    }

    // ── SP2 tests ─────────────────────────────────────────────────────────────

    #[test]
    fn referenced_descriptors_collects_special_operand_indices() {
        let compiled = compiled_with_one_descriptor_and_reference(0);
        let refs = referenced_descriptors(&compiled);
        assert!(refs.contains(&0));
        assert_eq!(refs.len(), 1);
    }

    #[test]
    fn referenced_descriptors_includes_root_output_aliases() {
        let compiled = compiled_with_alias_special_desc0_no_program_ref();
        let refs = referenced_descriptors(&compiled);
        assert!(refs.contains(&0), "alias Special operand must be a referenced descriptor");
    }

    #[test]
    fn validate_flags_out_of_range_reference() {
        let compiled = compiled_with_one_descriptor_and_reference(5);
        let (layer, (read, lookup, challenge), rows) = stub_layer_resolvers_rows();
        let r = make_resolvers_sp2(&read, &lookup, &challenge);
        let err = validate_special_bindings(&compiled, &layer, &rows, &r, &StubPeek(Ext::ZERO)).unwrap_err();
        assert_eq!(err, PeekError::DescriptorOutOfRange { desc: 5, table_len: 1 });
    }

    #[test]
    fn validate_flags_orphan_descriptor() {
        let compiled = compiled_with_two_descriptors_one_referenced();
        let (layer, (read, lookup, challenge), rows) = stub_layer_resolvers_rows();
        let r = make_resolvers_sp2(&read, &lookup, &challenge);
        let err = validate_special_bindings(&compiled, &layer, &rows, &r, &StubPeek(Ext::ZERO)).unwrap_err();
        assert_eq!(err, PeekError::OrphanDescriptor { desc: 1 });
    }

    #[test]
    fn validate_reports_mismatch_when_peek_ne_fold() {
        let compiled = compiled_peek_setup_desc0_origin_const(7);
        let (layer, (read, lookup, challenge), rows) = stub_layer_resolvers_rows();
        let r = make_resolvers_sp2(&read, &lookup, &challenge);
        let wrong = lift(Bf::from_u32_with_reduction(999));
        let err = validate_special_bindings(&compiled, &layer, &rows, &r, &StubPeek(wrong)).unwrap_err();
        assert!(matches!(err, PeekError::Mismatch { desc: 0, row, .. } if row == rows[0]),
                "got {err:?}");
    }

    #[test]
    fn validate_passes_when_peek_eq_fold_all_rows() {
        let compiled = compiled_peek_setup_desc0_origin_const(7);
        let (layer, (read, lookup, challenge), rows) = stub_layer_resolvers_rows();
        let r = make_resolvers_sp2(&read, &lookup, &challenge);
        let right = lift(Bf::from_u32_with_reduction(7));
        let n = validate_special_bindings(&compiled, &layer, &rows, &r, &StubPeek(right)).unwrap();
        assert_eq!(n, rows.len()); // 1 descriptor × rows
    }
}
