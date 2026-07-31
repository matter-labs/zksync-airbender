//! Scalar interpreters for the coefficient ISA (design §4, §9).
//!
//! Two of them, over one [`CoeffResolver`]:
//!
//!   * [`interpret_coeff_layer`] — the SEMANTIC reference. One row in,
//!     `(acc_c0, acc_c2)` out. There is no `T0`/`T2` role, no generic arithmetic
//!     accumulator, and no `acc_c1`: the round update recovers `c1` from the
//!     normalized claim. It deliberately knows nothing about the wire encoding.
//!   * [`interpret_lean_program`] — the LEAN interpreter of the segmented lean VM
//!     (`lean` module). It has no residency at all; what it adds is SEGMENTATION —
//!     the `K` per-warp term lists and the rule that exactly one of their partials
//!     carries `c_init`. The gate is identity with the semantic interpreter, at
//!     every `K`.
//!
//! The semantic reference is the ORACLE of the whole backward pipeline: every
//! parity ladder — lean CPU, and the CUDA executor — is stated against it.

use cs::gkr_compiler::dag_ir::{BwdRegime, Ext};
use field::Field;

use super::lean::{
    self, LEAN_CONT_OPCODES, LEAN_R0_OPCODES, LeanCodecError, LeanProgram, LeanTerm, SOURCE_NONE,
};
use super::limits::TermCategory;
use super::model::{
    CoeffError, CoeffLayer, CoeffTerm, CoefficientRecipeId, Projection, ProjectionId, SourceId,
    TermId,
};
use super::order::split_round_robin;

/// The two values a coefficient program needs from its environment.
///
/// [`CoeffResolver::coefficient`] is only ever called for a BANKED id: reserved
/// literals (`+1`/`-1`) are resolved by the interpreter itself, so an
/// implementation never has to allocate an evaluated bank entry for them.
///
/// [`CoeffResolver::source_pair`] returns the source's two named projections at
/// `row`, in that order: `(Endpoint0, Delta) = (s0, s1 - s0)`. It is a PAIR
/// because a native dual factor performs one physical source-pair resolution, not
/// two projection reads (§8).
pub trait CoeffResolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext;
    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext);
}

/// Interpret one row of `layer`, returning `(acc_c0, acc_c2)`.
///
/// `acc_c0` starts at the per-thread `c_init` initializer (or zero when the layer
/// has none) and `acc_c2` at zero; every term then adds its own contribution:
///
/// ```text
/// C0Linear(k, a0)        acc_c0 += k * a0
/// C2Product(k, da, db)   acc_c2 += k * da * db
/// DualProduct(k, A, B)   acc_c0 += k * A.s0 * B.s0 ; acc_c2 += k * A.ds * B.ds
/// ```
pub fn interpret_coeff_layer(
    layer: &CoeffLayer,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    let mut acc_c0 = match layer.c_init {
        Some(id) => coefficient(layer, id, resolver)?,
        None => Ext::ZERO,
    };
    let mut acc_c2 = Ext::ZERO;

    for term in &layer.terms {
        let k = coefficient(layer, term.coefficient(), resolver)?;
        match term {
            CoeffTerm::C0Linear { id, value, .. } => {
                let (e0, _) = projection(layer, *id, *value, Projection::Endpoint0, row, resolver)?;
                let mut v = k;
                v.mul_assign(&e0);
                acc_c0.add_assign(&v);
            }
            CoeffTerm::C2Product { id, lhs, rhs, .. } => {
                let (_, dl) = projection(layer, *id, *lhs, Projection::Delta, row, resolver)?;
                let (_, dr) = projection(layer, *id, *rhs, Projection::Delta, row, resolver)?;
                let mut v = k;
                v.mul_assign(&dl);
                v.mul_assign(&dr);
                acc_c2.add_assign(&v);
            }
            CoeffTerm::DualProduct { lhs, rhs, .. } => {
                let (l0, ld) = source_pair(layer, *lhs, row, resolver)?;
                let (r0, rd) = source_pair(layer, *rhs, row, resolver)?;
                let mut c0 = k;
                c0.mul_assign(&l0);
                c0.mul_assign(&r0);
                acc_c0.add_assign(&c0);
                let mut c2 = k;
                c2.mul_assign(&ld);
                c2.mul_assign(&rd);
                acc_c2.add_assign(&c2);
            }
        }
    }
    Ok((acc_c0, acc_c2))
}

/// Reserved literals resolve internally (no bank entry, no resolver call); every
/// other id is validated against the bank before the resolver is asked. A banked
/// zero recipe is a compiler error, so it is rejected rather than evaluated.
fn coefficient(
    layer: &CoeffLayer,
    id: CoefficientRecipeId,
    resolver: &impl CoeffResolver,
) -> Result<Ext, CoeffError> {
    if let Some(v) = id.literal() {
        return Ok(v);
    }
    match layer.banked_recipe(id) {
        None => Err(CoeffError::UnknownCoefficient { id }),
        Some(r) if r.is_zero() => Err(CoeffError::EncodedZeroCoefficient { id }),
        Some(_) => Ok(resolver.coefficient(id)),
    }
}

fn source_pair(
    layer: &CoeffLayer,
    id: SourceId,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    if layer.source(id).is_none() {
        return Err(CoeffError::UnknownSource { id });
    }
    Ok(resolver.source_pair(id, row))
}

/// Resolve a projection, rejecting a role its opcode cannot consume.
fn projection(
    layer: &CoeffLayer,
    term: TermId,
    p: ProjectionId,
    expected: Projection,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    if p.projection != expected {
        return Err(CoeffError::ProjectionRoleMismatch { term, expected, found: p.projection });
    }
    source_pair(layer, p.source, row, resolver)
}

// ── The lean segmented interpreter ───────────────────────────────────────────

/// Everything [`interpret_lean_program`] can reject.
///
/// Three sources, kept apart because they are three different statements: the
/// WIRE is malformed ([`LeanCodecError`]), a well-formed record does not fit the
/// LAYER it was handed ([`CoeffError`], raised by the very helpers
/// [`interpret_coeff_layer`] uses), or the layer contradicts its own REGIME —
/// which is neither, and is why this enum has a third variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanInterpError {
    /// A defect in the words themselves: [`lean::decode_program`]'s length and
    /// reserved-word rules, a class dead in `layer.regime`, or a two-source class
    /// carrying [`SOURCE_NONE`].
    Codec(LeanCodecError),
    /// A well-formed record the layer cannot serve, reported by the SAME
    /// `coefficient` / `source_pair` helpers [`interpret_coeff_layer`] uses: an
    /// unbanked coefficient, an encoded zero, a slot past `layer.sources`.
    Coeff(CoeffError),
    /// `layer.c_init` is `Some` in the R0 regime.
    ///
    /// R0 lowering DROPS the spine's scalar addends
    /// ([`lower_coeff_layer`](super::lower::lower_coeff_layer)) because at R0 they
    /// are already inside the materialized output value the `acc_c0` shortcut
    /// reads, so seeding one here would double-count them (§5.3). No
    /// [`CoeffError`] variant says this — it is a property of the regime, not of
    /// any id, record or term.
    CInitAtR0 { id: CoefficientRecipeId },
}

impl From<LeanCodecError> for LeanInterpError {
    fn from(error: LeanCodecError) -> Self {
        LeanInterpError::Codec(error)
    }
}

impl From<CoeffError> for LeanInterpError {
    fn from(error: CoeffError) -> Self {
        LeanInterpError::Coeff(error)
    }
}

/// Interpret one row of a LEAN program under the `k`-way segmentation the launch
/// performs, returning `(acc_c0, acc_c2)`.
///
/// `k` is the number of per-warp term lists:
/// [`split_round_robin`](super::order::split_round_robin) over the decoded record
/// POSITIONS gives list `w` positions `w, w+k, w+2k, …` (§3), each list
/// accumulates its own partial pair in isolation, and the result is the sum of the
/// `k` partials. Field addition is exact, so the value is the same for every `k` —
/// segmentation is invisible to parity, which is what lets this be the oracle a
/// kernel must match bit-for-bit at whatever `K` it launches.
///
/// `c_init` seeds EXACTLY ONE partial — list 0's `acc_c0` (§5.3). Seeding each
/// list would reduce to `K * c_init`; list 0 is seeded even when it is empty
/// (`k` above the term count), so the seed lands exactly once for every `k`.
///
/// SEMANTIC layer only: every operand resolves through
/// [`CoeffResolver::source_pair`] at the projection its CLASS implies, since no
/// projection travels on the lean wire. Raw-BF inline folds, procedural synthesis
/// and the prologue are round-binding concerns and are deliberately absent.
///
/// # Panics
///
/// If `k == 0` — there is no zero-warp launch.
pub fn interpret_lean_program(
    program: &LeanProgram,
    layer: &CoeffLayer,
    row: usize,
    resolver: &impl CoeffResolver,
    k: usize,
) -> Result<(Ext, Ext), LeanInterpError> {
    let records = lean::decode_program(program)?;
    let seed = match layer.c_init {
        Some(id) if layer.regime == BwdRegime::R0 => return Err(LeanInterpError::CInitAtR0 { id }),
        Some(id) => coefficient(layer, id, resolver)?,
        None => Ext::ZERO,
    };
    // Split the POSITIONS, not the records: an error then names a record by its
    // position in the program, which is the only index a reader can act on.
    let positions: Vec<usize> = (0..records.len()).collect();
    let mut acc_c0 = Ext::ZERO;
    let mut acc_c2 = Ext::ZERO;
    for (list, list_positions) in split_round_robin(&positions, k).iter().enumerate() {
        // §5.3: ONE partial carries the seed. `k` seeded partials would reduce to
        // `k * c_init`.
        let mut partial_c0 = if list == 0 { seed } else { Ext::ZERO };
        let mut partial_c2 = Ext::ZERO;
        for &position in list_positions {
            lean_record(
                layer,
                position,
                &records[position],
                row,
                resolver,
                &mut partial_c0,
                &mut partial_c2,
            )?;
        }
        acc_c0.add_assign(&partial_c0);
        acc_c2.add_assign(&partial_c2);
    }
    Ok((acc_c0, acc_c2))
}

/// Add one decoded record's contribution to its list's partial pair.
///
/// The per-kind algebra is [`interpret_coeff_layer`]'s, term for term and
/// multiplication for multiplication: a `C0Linear` class consumes its source's
/// `Endpoint0`, a `C2Product` class the two deltas, and the native dual factor
/// both projections of both sources. A mixed `C2Product` is the one place the wire
/// reorders operands — the encoder normalizes the base-field factor into
/// `source_a` — and field multiplication is exact and commutative, so the product
/// is the same element either way. A squared product resolves its source twice,
/// exactly as the semantic interpreter does; that a kernel loads it once is a
/// physical property of the kernel and not of the value.
fn lean_record(
    layer: &CoeffLayer,
    position: usize,
    record: &LeanTerm,
    row: usize,
    resolver: &impl CoeffResolver,
    acc_c0: &mut Ext,
    acc_c2: &mut Ext,
) -> Result<(), LeanInterpError> {
    let class = u16::from(record.class);
    let category = lean_category(layer.regime, class)
        .ok_or(LeanCodecError::ClassNotInRegime { term: position, opcode: class })?;
    let k = coefficient(layer, CoefficientRecipeId(u32::from(record.coeff)), resolver)?;
    let a = SourceId(u32::from(record.source_a));
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => {
            let (e0, _) = source_pair(layer, a, row, resolver)?;
            let mut v = k;
            v.mul_assign(&e0);
            acc_c0.add_assign(&v);
        }
        TermCategory::C2ProductBfBf
        | TermCategory::C2ProductBfE4
        | TermCategory::C2ProductE4E4 => {
            let b = second_source(position, record)?;
            let (_, da) = source_pair(layer, a, row, resolver)?;
            let (_, db) = source_pair(layer, b, row, resolver)?;
            let mut v = k;
            v.mul_assign(&da);
            v.mul_assign(&db);
            acc_c2.add_assign(&v);
        }
        TermCategory::DualProductE4 => {
            let b = second_source(position, record)?;
            let (a0, ad) = source_pair(layer, a, row, resolver)?;
            let (b0, bd) = source_pair(layer, b, row, resolver)?;
            let mut c0 = k;
            c0.mul_assign(&a0);
            c0.mul_assign(&b0);
            acc_c0.add_assign(&c0);
            let mut c2 = k;
            c2.mul_assign(&ad);
            c2.mul_assign(&bd);
            acc_c2.add_assign(&c2);
        }
        // The lean class tables carry no `Move` row — `lean.rs`'s
        // `is_densified_frozen_table` proves it when the crate compiles — so
        // `lean_category` cannot return one.
        TermCategory::MoveBf | TermCategory::MoveE4 => {
            unreachable!("the lean class tables have no move rows")
        }
    }
    Ok(())
}

/// The category a lean class names in `regime`, or `None` for a dead class.
///
/// The tables are the wire ABI and are public, so this and
/// [`lean::validate_program`] read the same rows; only the `find` is spelled
/// twice.
fn lean_category(regime: BwdRegime, class: u16) -> Option<TermCategory> {
    let table = match regime {
        BwdRegime::R0 => LEAN_R0_OPCODES,
        BwdRegime::Ext => LEAN_CONT_OPCODES,
    };
    table.iter().find(|(listed, _)| *listed == class).map(|(_, category)| *category)
}

/// The second operand slot of a two-source class. The sentinel there is a record
/// its class cannot execute, so it is rejected rather than read as slot `0xFFFF`.
///
/// The mirror rule — a real slot in `source_b` on a ONE-source class — is
/// [`lean::validate_program`]'s: the class has no factor for it, so execution
/// ignores the word exactly as a kernel does.
fn second_source(position: usize, record: &LeanTerm) -> Result<SourceId, LeanCodecError> {
    if record.source_b == SOURCE_NONE {
        return Err(LeanCodecError::SourceBMissing { term: position });
    }
    Ok(SourceId(u32::from(record.source_b)))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::path::PathBuf;

    use cs::gkr_compiler::GKRCircuitArtifact;
    use cs::gkr_compiler::dag_ir::{
        Bf, DagLayer, FieldKind, ReadPlace, bwd_roots, lower_dag, validate,
    };
    use field::baby_bear::base::BabyBearField;
    use field::{FieldExtension, PrimeField};
    use rayon::prelude::*;

    use super::*;
    use crate::bwd::coeff::limits::in_scope;
    use crate::bwd::coeff::lower::lower_coeff_layer;
    use crate::bwd::coeff::model::{CoeffSource, NormalizedCoefficientRecipe};
    use crate::bwd::coeff::order::order_terms;
    use crate::bwd::distill::distill;
    use crate::bwd::source::OriginLeaf;
    use crate::fwd::compile::build_cross_layer_field_map;

    /// Segmentation widths every claim is made at. `1` is the unsegmented case,
    /// `16` exceeds the term count of the synthetic layers so the tail lists are
    /// empty — the path where a seed added per list is most visible.
    const KS: [usize; 3] = [1, 4, 16];
    /// Rows sampled per coordinate.
    const ROWS: [usize; 3] = [0, 1, 37];

    /// The 12 pinned Global-Constraints layouts — the same list, in the same
    /// order, as `tests/common`'s `FIXTURES`, which every other corpus gate uses.
    const FIXTURES: &[&str] = &[
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "blake2_g_function_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "inits_and_teardowns_preprocessed_layout_gkr.json",
        "jump_branch_slt_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
        "mem_subword_only_layout_gkr.json",
        "mem_word_only_layout_gkr.json",
        "shift_binop_layout_gkr.json",
        "unsigned_mul_div_layout_gkr.json",
        "unified_reduced_machine_layout_gkr.json",
    ];

    // ── Fixture loading ──────────────────────────────────────────────────────

    fn load_fixture(name: &str) -> GKRCircuitArtifact<BabyBearField> {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
        let path = dir.join(name);
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
    }

    /// Every backward-bearing layer of `name`, as `(layer index, layer, cross-layer
    /// field map)`. The map is a whole-circuit property, so the same clone rides
    /// each tuple (matching `distill(&layer, regime, &cross, None)`).
    fn layers_with_bwd_roots(name: &str) -> Vec<(usize, DagLayer, HashMap<ReadPlace, FieldKind>)> {
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let cross = build_cross_layer_field_map(&dag);
        dag.layers
            .iter()
            .enumerate()
            .filter(|(_, layer)| !bwd_roots(layer).is_empty())
            .map(|(li, layer)| (li, layer.clone(), cross.clone()))
            .collect()
    }

    // ── A deterministic resolver both interpreters share ─────────────────────

    const FNV_OFFSET: u32 = 0x811c_9dc5;
    const FNV_PRIME: u32 = 0x0100_0193;

    fn fnv(words: &[u32]) -> u32 {
        let mut h = FNV_OFFSET;
        for w in words {
            for b in w.to_le_bytes() {
                h ^= u32::from(b);
                h = h.wrapping_mul(FNV_PRIME);
            }
        }
        h
    }

    fn bf(v: u32) -> Bf {
        Bf::from_u32_with_reduction(v)
    }

    fn lift(v: Bf) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(v)
    }

    /// Four independent base digits, so an `Ext` value is genuinely
    /// extension-valued and a base/extension confusion cannot pass unnoticed.
    fn ext(tag: u32, a: u32, b: u32) -> Ext {
        let coeffs: [Bf; 4] = std::array::from_fn(|i| bf(fnv(&[tag, a, b, i as u32])));
        <Ext as FieldExtension<Bf>>::from_coeffs(coeffs)
    }

    /// A BF source resolves BASE-EMBEDDED, so a class that claims a base-field
    /// factor is handed one.
    struct Pseudo<'a> {
        layer: &'a CoeffLayer,
        seed: u32,
    }

    impl CoeffResolver for Pseudo<'_> {
        fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
            ext(0xc0ef, self.seed, id.0)
        }

        fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
            let row = row as u32;
            match self.layer.sources[id.0 as usize].field {
                FieldKind::Base => (
                    lift(bf(fnv(&[0xb0, self.seed ^ id.0, row]))),
                    lift(bf(fnv(&[0xb1, self.seed ^ id.0, row]))),
                ),
                FieldKind::Ext => {
                    (ext(0x5000, self.seed ^ id.0, row), ext(0x5001, self.seed ^ id.0, row))
                }
            }
        }
    }

    // ── Synthetic layers ─────────────────────────────────────────────────────

    fn layer(
        regime: BwdRegime,
        sources: &[FieldKind],
        recipes: usize,
        terms: Vec<CoeffTerm>,
    ) -> CoeffLayer {
        CoeffLayer {
            regime,
            c_init: None,
            // Every bank entry must be non-zero: an encoded zero coefficient is a
            // compiler error both interpreters reject.
            coefficients: (0..recipes)
                .map(|index| NormalizedCoefficientRecipe::scalar(bf(3 + index as u32)))
                .collect(),
            sources: sources
                .iter()
                .enumerate()
                .map(|(column, &field)| CoeffSource {
                    origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }),
                    field,
                })
                .collect(),
            terms,
            groups: Vec::new(),
            immediates: Vec::new(),
        }
    }

    fn c0(index: u32, coefficient: u32, source: u32, field: FieldKind) -> CoeffTerm {
        CoeffTerm::C0Linear {
            id: TermId(index),
            coefficient: CoefficientRecipeId(coefficient),
            value: ProjectionId::endpoint0(SourceId(source)),
            field,
        }
    }

    fn c2(index: u32, coefficient: u32, lhs: (u32, FieldKind), rhs: (u32, FieldKind)) -> CoeffTerm {
        CoeffTerm::C2Product {
            id: TermId(index),
            coefficient: CoefficientRecipeId(coefficient),
            lhs: ProjectionId::delta(SourceId(lhs.0)),
            rhs: ProjectionId::delta(SourceId(rhs.0)),
            lhs_field: lhs.1,
            rhs_field: rhs.1,
        }
    }

    fn dual(index: u32, coefficient: u32, lhs: u32, rhs: u32) -> CoeffTerm {
        CoeffTerm::DualProduct {
            id: TermId(index),
            coefficient: CoefficientRecipeId(coefficient),
            lhs: SourceId(lhs),
            rhs: SourceId(rhs),
        }
    }

    /// Seven continuation terms over three sources — both live `Ext` classes, a
    /// squared native dual factor, both reserved literals and both bank entries —
    /// seeded with a banked, resolver-visible `c_init`.
    fn seeded_ext_layer() -> CoeffLayer {
        let terms = vec![
            c0(0, CoefficientRecipeId::ONE.0, 0, FieldKind::Ext),
            dual(1, CoefficientRecipeId::NEG_ONE.0, 1, 2),
            c0(2, 2, 1, FieldKind::Ext),
            dual(3, 3, 0, 0),
            c0(4, CoefficientRecipeId::ONE.0, 2, FieldKind::Ext),
            dual(5, 2, 2, 1),
            c0(6, 3, 0, FieldKind::Ext),
        ];
        CoeffLayer {
            c_init: Some(CoefficientRecipeId(2)),
            ..layer(BwdRegime::Ext, &[FieldKind::Ext; 3], 2, terms)
        }
    }

    /// One hand-spelled record, as its own program.
    fn record(class: u16, coeff: u16, source_a: u16, source_b: u16) -> LeanProgram {
        LeanProgram {
            words: vec![(class << lean::LEAN_CLASS_SHIFT) | coeff, source_a, source_b, 0],
            term_count: 1,
        }
    }

    /// The per-warp sub-programs `split_round_robin` produces, each a standalone
    /// lean program: the WORD stream split at exactly the record positions
    /// [`interpret_lean_program`] splits at.
    fn sublists(program: &LeanProgram, k: usize) -> Vec<LeanProgram> {
        let records: Vec<[u16; lean::LEAN_WORDS_PER_TERM]> = program
            .words
            .chunks_exact(lean::LEAN_WORDS_PER_TERM)
            .map(|record| record.try_into().expect("fixed-width records"))
            .collect();
        split_round_robin(&records, k)
            .into_iter()
            .map(|list| LeanProgram {
                term_count: list.len(),
                words: list.into_iter().flatten().collect(),
            })
            .collect()
    }

    // ── The corpus gate ──────────────────────────────────────────────────────

    /// The central claim, corpus-wide: on every in-scope `(circuit, layer,
    /// regime)` coordinate the lean program in the COMMITTED term order evaluates
    /// to exactly what the semantic interpreter produces, at every `k`. Both sides
    /// see the same coefficients and the same source pairs, so a difference is a
    /// codec or segmentation defect and nothing else.
    ///
    /// The SEEDED count is pinned too, because the K-way seeding rule is only
    /// under test on a coordinate that carries a `c_init`: were that count to fall
    /// to zero the parity assertion would still pass at every `k` and would prove
    /// nothing about §5.3.
    #[test]
    fn lean_and_semantic_interpreters_agree_over_the_corpus() {
        let (coordinates, seeded) = FIXTURES
            .par_iter()
            .map(|name| {
                let mut count = 0usize;
                let mut seeded = 0usize;
                for (li, canonical, cross) in layers_with_bwd_roots(name) {
                    for regime in [BwdRegime::R0, BwdRegime::Ext] {
                        let label = if regime == BwdRegime::R0 { "R0" } else { "Ext" };
                        let tag = format!("{name} L{li} {label}");
                        let distilled = distill(&canonical, regime, &cross, None);
                        let layer = lower_coeff_layer(&canonical, &distilled)
                            .unwrap_or_else(|e| panic!("[{tag}] lowering: {e:?}"));
                        let program = lean::encode_program(&layer, &order_terms(&layer))
                            .unwrap_or_else(|e| panic!("[{tag}] encode: {e:?}"));
                        assert_eq!(
                            lean::validate_program(&program, &layer),
                            Ok(()),
                            "[{tag}] the encoder emits a program the validator accepts",
                        );
                        let resolver = Pseudo { layer: &layer, seed: (li as u32) << 8 | 0x5a };
                        for row in ROWS {
                            let semantic = interpret_coeff_layer(&layer, row, &resolver)
                                .unwrap_or_else(|e| panic!("[{tag}] semantic: {e:?}"));
                            for k in KS {
                                let lean =
                                    interpret_lean_program(&program, &layer, row, &resolver, k)
                                        .unwrap_or_else(|e| panic!("[{tag} k{k}] lean: {e:?}"));
                                assert_eq!(
                                    lean, semantic,
                                    "[{tag} row {row}] k={k} disagrees with the semantic \
                                     interpreter",
                                );
                            }
                        }
                        count += 1;
                        seeded += usize::from(layer.c_init.is_some());
                    }
                }
                (count, seeded)
            })
            .reduce(|| (0, 0), |a, b| (a.0 + b.0, a.1 + b.1));
        assert_eq!(coordinates, in_scope::COORDINATES, "every in-scope coordinate was covered");
        /// Coordinates carrying a `c_init`, measured: 27 of the 57 `Ext` ones. R0
        /// contributes ZERO, since its lowering drops the spine's scalar addends —
        /// which is also why nothing in the corpus can reach
        /// [`LeanInterpError::CInitAtR0`] and that rule is pinned synthetically.
        const SEEDED_COORDINATES: usize = 27;
        assert_eq!(seeded, SEEDED_COORDINATES, "seeded coordinates moved");
    }

    // ── The `c_init` seeding contract ────────────────────────────────────────

    /// `c_init` seeds exactly ONE partial. The mis-seeded variant is built from
    /// the SAME split — every list run as its own one-list program, so every
    /// partial carries the seed — and it is off by exactly `(k-1) * c_init` in
    /// `acc_c0` and by nothing at all in `acc_c2`. That is the `K * c_init` shape
    /// the design names as the known failure, and this is the gate that catches it.
    #[test]
    fn c_init_seeds_exactly_one_partial() {
        let layer = seeded_ext_layer();
        let program = lean::encode_program(&layer, &order_terms(&layer)).expect("a legal layer");
        assert_eq!(lean::validate_program(&program, &layer), Ok(()));
        let resolver = Pseudo { layer: &layer, seed: 0x77 };
        let c_init = resolver.coefficient(layer.c_init.expect("a seeded layer"));
        assert_ne!(c_init, Ext::ZERO, "the fixture must make the seed observable");

        for row in ROWS {
            let semantic = interpret_coeff_layer(&layer, row, &resolver).expect("semantic");
            for k in KS {
                let lean =
                    interpret_lean_program(&program, &layer, row, &resolver, k).expect("lean");
                assert_eq!(lean, semantic, "row {row} k={k}");

                let mut misseeded = (Ext::ZERO, Ext::ZERO);
                for sub in sublists(&program, k) {
                    let (c0, c2) = interpret_lean_program(&sub, &layer, row, &resolver, 1)
                        .expect("a sub-list is a legal program");
                    misseeded.0.add_assign(&c0);
                    misseeded.1.add_assign(&c2);
                }
                let mut expected = semantic.0;
                for _ in 1..k {
                    expected.add_assign(&c_init);
                }
                assert_eq!(misseeded.0, expected, "row {row} k={k}: divergence is (k-1)*c_init");
                assert_eq!(misseeded.1, semantic.1, "row {row} k={k}: acc_c2 carries no seed");
                if k > 1 {
                    assert_ne!(misseeded.0, lean.0, "row {row} k={k}: K*c_init must be caught");
                }
            }
        }
    }

    /// R0 lowering DROPS the spine's scalar addends (`lower.rs`'s `lower_c_init`),
    /// so a seed in that regime is a contradiction rather than an initializer.
    #[test]
    fn r0_rejects_a_c_init() {
        let terms = vec![
            c0(0, CoefficientRecipeId::ONE.0, 0, FieldKind::Base),
            c2(1, 2, (0, FieldKind::Base), (1, FieldKind::Ext)),
        ];
        let unseeded = layer(BwdRegime::R0, &[FieldKind::Base, FieldKind::Ext], 1, terms);
        let id = CoefficientRecipeId(2);
        let seeded = CoeffLayer { c_init: Some(id), ..unseeded.clone() };
        let program =
            lean::encode_program(&unseeded, &order_terms(&unseeded)).expect("a legal R0 layer");
        // The two layers differ only in `c_init`, so one resolver serves both.
        let resolver = Pseudo { layer: &unseeded, seed: 0x88 };

        let semantic = interpret_coeff_layer(&unseeded, 0, &resolver).expect("semantic");
        assert_eq!(
            interpret_lean_program(&program, &unseeded, 0, &resolver, 4),
            Ok(semantic),
            "an unseeded R0 layer runs, and agrees",
        );
        assert_eq!(
            interpret_lean_program(&program, &seeded, 0, &resolver, 4),
            Err(LeanInterpError::CInitAtR0 { id }),
        );
    }

    // ── Rejections ───────────────────────────────────────────────────────────

    /// A defect the WIRE carries reports as `Codec`; a record the LAYER cannot
    /// serve reports the semantic interpreter's own `CoeffError`, because it
    /// travels through the same two helpers.
    #[test]
    fn lean_rejections_name_their_source() {
        let terms = vec![
            c0(0, CoefficientRecipeId::ONE.0, 0, FieldKind::Ext),
            dual(1, CoefficientRecipeId::NEG_ONE.0, 0, 1),
        ];
        let layer = layer(BwdRegime::Ext, &[FieldKind::Ext; 2], 1, terms);
        let resolver = Pseudo { layer: &layer, seed: 0x99 };
        let run = |program: &LeanProgram, k: usize| {
            interpret_lean_program(program, &layer, 0, &resolver, k)
        };

        // Class 2 is dead in the continuation regime.
        assert_eq!(
            run(&record(2, 0, 0, SOURCE_NONE), 1),
            Err(LeanInterpError::Codec(LeanCodecError::ClassNotInRegime { term: 0, opcode: 2 })),
        );
        // A two-source class with no second source cannot execute.
        assert_eq!(
            run(&record(1, 0, 0, SOURCE_NONE), 1),
            Err(LeanInterpError::Codec(LeanCodecError::SourceBMissing { term: 0 })),
        );
        // `decode_program`'s own rules still apply.
        assert_eq!(
            run(&LeanProgram { words: vec![0, 0, 0], term_count: 1 }, 1),
            Err(LeanInterpError::Codec(LeanCodecError::TruncatedStream { words: 3 })),
        );
        // A slot past the source table and an unbanked coefficient are the
        // SEMANTIC interpreter's errors, reported by the helpers it shares.
        assert_eq!(
            run(&record(0, 0, 7, SOURCE_NONE), 1),
            Err(LeanInterpError::Coeff(CoeffError::UnknownSource { id: SourceId(7) })),
        );
        let past = CoefficientRecipeId::RESERVED + layer.coefficients.len() as u32;
        assert_eq!(
            run(&record(0, past as u16, 0, SOURCE_NONE), 1),
            Err(LeanInterpError::Coeff(CoeffError::UnknownCoefficient {
                id: CoefficientRecipeId(past),
            })),
        );

        // The reported index is the record's position in the PROGRAM, not its
        // position inside the list the split put it in.
        let mut words = record(0, 0, 0, SOURCE_NONE).words;
        words.extend(record(0, 0, 0, SOURCE_NONE).words);
        words.extend(record(2, 0, 0, SOURCE_NONE).words);
        assert_eq!(
            run(&LeanProgram { words, term_count: 3 }, 2),
            Err(LeanInterpError::Codec(LeanCodecError::ClassNotInRegime { term: 2, opcode: 2 })),
        );
    }

    /// There is no zero-warp launch.
    #[test]
    #[should_panic(expected = "at least one list")]
    fn zero_lists_is_not_a_launch() {
        let layer = seeded_ext_layer();
        let program = lean::encode_program(&layer, &order_terms(&layer)).expect("a legal layer");
        let resolver = Pseudo { layer: &layer, seed: 0xaa };
        let _ = interpret_lean_program(&program, &layer, 0, &resolver, 0);
    }

    /// The encoder normalizes a mixed `C2Product` to BF-FIRST, so for a transposed
    /// term the lean record multiplies the two deltas in the opposite order from
    /// the IR. Exact field multiplication commutes, and the gate says so on the
    /// value rather than on the argument.
    #[test]
    fn a_transposed_mixed_product_matches_the_semantic_term() {
        let sources = [FieldKind::Base, FieldKind::Ext];
        let (base, extension) = ((0, FieldKind::Base), (1, FieldKind::Ext));
        let mut values = Vec::new();
        for (lhs, rhs) in [(base, extension), (extension, base)] {
            let layer = layer(BwdRegime::R0, &sources, 1, vec![c2(0, 2, lhs, rhs)]);
            let program = lean::encode_program(&layer, &[TermId(0)]).expect("a legal term");
            let resolver = Pseudo { layer: &layer, seed: 0xa1 };
            for row in ROWS {
                let semantic = interpret_coeff_layer(&layer, row, &resolver).expect("semantic");
                let lean =
                    interpret_lean_program(&program, &layer, row, &resolver, 1).expect("lean");
                assert_eq!(lean, semantic, "row {row}, operands {lhs:?} x {rhs:?}");
            }
            values.push(interpret_lean_program(&program, &layer, 0, &resolver, 1).expect("lean"));
        }
        assert_eq!(values[0], values[1], "the wire's BF-first normalization is value-neutral");
        assert_ne!(values[0].1, Ext::ZERO, "the fixture must make the product observable");
    }
}
