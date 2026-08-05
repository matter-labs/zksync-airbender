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

use field::{Field, FieldExtension, PrimeField};
use gkr_eval_ir::{Bf, Ext};

use super::group;
use super::lean::{
    self, LEAN_CONT_OPCODES, LEAN_R0_OPCODES, LeanAtom, LeanCodecError, LeanProgram, LeanTerm,
    SOURCE_NONE,
};
use super::limits::TermCategory;
use super::model::{
    CoeffError, CoeffLayer, CoeffTerm, CoefficientRecipeId, ImmediateId, Projection, ProjectionId,
    SourceId, TermId,
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
///
/// A GROUPED layer (§4.1) changes the SHAPE of that sum, never its value. A
/// group's members carry the group's CORE as their coefficient id plus their own
/// base-field immediate, so the members are summed FIRST and the core multiplies
/// each accumulator side once:
///
/// ```text
/// group(core, members)   acc_c0 += core * SUM imm_m * <member m's c0 part>
///                        acc_c2 += core * SUM imm_m * <member m's c2 part>
/// ```
///
/// where a member's parts are exactly the products its own term kind contributes
/// above, with the per-term coefficient factored out. `has_c0` / `has_c2` say which
/// sides the group feeds; the other sum is zero, and its core multiplication is
/// skipped rather than performed against zero.
///
/// This is the same field element the ungrouped layer produces — `SUM_m (imm_m *
/// core) * v_m == core * SUM_m imm_m * v_m` is distributivity, and field
/// arithmetic is exact, so there is no tolerance in which a dropped immediate or a
/// double-served member could hide. The corpus gate
/// (`bwd_coeff_corpus.rs::grouped_semantics_match_ungrouped_bit_for_bit`) asserts
/// it limb for limb on every `Ext` coordinate.
///
/// An UNGROUPED layer takes exactly the path it always did: `layer.groups` is
/// empty, every term is plain, and the group loop does not run.
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

    // A grouped member is NOT a plain term: its `coefficient()` is its group's
    // core, so evaluating it here would silently drop its immediate. The mask is
    // built over `TermId` — which is the term's own index, `layer.terms` being
    // dense (`terms[i].id() == TermId(i)`) — and the group loop below serves every
    // masked term exactly once, since a term belongs to at most one group.
    let mut grouped = vec![false; layer.terms.len()];
    for group in &layer.groups {
        for member in &group.members {
            grouped[member.term.0 as usize] = true;
        }
    }

    for term in &layer.terms {
        if grouped[term.id().0 as usize] {
            continue;
        }
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

    // ONE core multiplication per side per group, instead of one per member. The
    // order the members are summed in is irrelevant — the field is exact — so this
    // loop's position after the plain terms is a readability choice, not a semantic
    // one.
    for group in &layer.groups {
        let core = coefficient(layer, group.core, resolver)?;
        let mut s_c0 = Ext::ZERO;
        let mut s_c2 = Ext::ZERO;
        for member in &group.members {
            let imm = immediate_value(layer, member.immediate)?;
            let term = &layer.terms[member.term.0 as usize];
            match term {
                CoeffTerm::C0Linear { id, value, .. } => {
                    let (e0, _) =
                        projection(layer, *id, *value, Projection::Endpoint0, row, resolver)?;
                    accumulate_imm(&mut s_c0, member.immediate, imm, e0);
                }
                CoeffTerm::C2Product { id, lhs, rhs, .. } => {
                    let (_, dl) = projection(layer, *id, *lhs, Projection::Delta, row, resolver)?;
                    let (_, dr) = projection(layer, *id, *rhs, Projection::Delta, row, resolver)?;
                    let mut v = dl;
                    v.mul_assign(&dr);
                    accumulate_imm(&mut s_c2, member.immediate, imm, v);
                }
                CoeffTerm::DualProduct { lhs, rhs, .. } => {
                    let (l0, ld) = source_pair(layer, *lhs, row, resolver)?;
                    let (r0, rd) = source_pair(layer, *rhs, row, resolver)?;
                    let mut c0 = l0;
                    c0.mul_assign(&r0);
                    accumulate_imm(&mut s_c0, member.immediate, imm, c0);
                    let mut c2 = ld;
                    c2.mul_assign(&rd);
                    accumulate_imm(&mut s_c2, member.immediate, imm, c2);
                }
            }
        }
        if group.has_c0 {
            let mut v = core;
            v.mul_assign(&s_c0);
            acc_c0.add_assign(&v);
        }
        if group.has_c2 {
            let mut v = core;
            v.mul_assign(&s_c2);
            acc_c2.add_assign(&v);
        }
    }
    Ok((acc_c0, acc_c2))
}

/// The `Ext`-lifted base-field value a member's [`ImmediateId`] denotes.
///
/// The id space itself is decoded by [`group::immediate_value`] — the crate's ONE
/// decoder of it — so the interpreter cannot disagree with the transform that
/// minted the id, and an id past the layer's table is rejected here exactly as
/// [`coefficient`] rejects an unbanked coefficient.
///
/// The lift is unconditional, including for the two reserved literals: what `±1`
/// saves is a MULTIPLICATION, and that saving lives in [`accumulate_imm`].
fn immediate_value(layer: &CoeffLayer, id: ImmediateId) -> Result<Ext, CoeffError> {
    let value = group::immediate_value(layer, id).ok_or(CoeffError::UnknownImmediate { id })?;
    Ok(<Ext as FieldExtension<Bf>>::from_base(
        Bf::from_u32_with_reduction(value),
    ))
}

/// Add `imm * v` to a group's per-side sum, spending NO multiplication on the two
/// reserved immediates: `+1` is an addition and `-1` a subtraction (§4.4 — a
/// member's immediate is meant to be cheaper than the `Ext` coefficient it
/// replaced, and for `±1` it is free).
///
/// `imm` is ignored on both fast paths, so a wrong lift of a reserved id cannot
/// change a value; the SIGN comes from the id, which is the only thing that carries
/// it.
fn accumulate_imm(acc: &mut Ext, id: ImmediateId, imm: Ext, v: Ext) {
    if id == ImmediateId::ONE {
        acc.add_assign(&v);
    } else if id == ImmediateId::NEG_ONE {
        acc.sub_assign(&v);
    } else {
        let mut scaled = imm;
        scaled.mul_assign(&v);
        acc.add_assign(&scaled);
    }
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
        return Err(CoeffError::ProjectionRoleMismatch {
            term,
            expected,
            found: p.projection,
        });
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
/// `k` is the number of per-warp lists:
/// [`split_round_robin`](super::order::split_round_robin) over the decoded ATOM
/// indices gives list `w` atoms `w, w+k, w+2k, …` (§3), each list accumulates its
/// own partial pair in isolation, and the result is the sum of the `k` partials.
/// Field addition is exact, so the value is the same for every `k` — segmentation
/// is invisible to parity, which is what lets this be the oracle a kernel must
/// match bit-for-bit at whatever `K` it launches.
///
/// The unit of the split is the ATOM ([`LeanAtom`]), not the record: a GROUP is one
/// indivisible unit of work, since its `core * SUM imm_m * v_m` shape only exists
/// while its members share a partial. That is also why this round-robin is not the
/// deal a kernel performs — §6: ANY whole-atom partition yields the same field
/// element, so list IDENTITY is deliberately not part of the contract and is never
/// compared against the GPU's descriptor deal. A group-free program (every R0
/// program, and every continuation program the ungrouped pipeline emits) has one
/// atom per record, so the split is position-identical to the pre-group one.
///
/// `c_init` seeds EXACTLY ONE partial — list 0's `acc_c0` (§5.3). Seeding each
/// list would reduce to `K * c_init`; list 0 is seeded even when it is empty
/// (`k` above the atom count), so the seed lands exactly once for every `k`.
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
    let atoms = lean::decode_atoms(program, layer.regime)?;
    let seed = match layer.c_init {
        Some(id) if layer.regime == crate::BwdRegime::R0 => {
            return Err(LeanInterpError::CInitAtR0 { id });
        }
        Some(id) => coefficient(layer, id, resolver)?,
        None => Ext::ZERO,
    };
    // The RECORD index each atom starts at, which is the index the codec's errors
    // speak in (a header counts as a record, exactly as `LeanCodecError` documents)
    // — so a reject names the offending record's offset in the program, the only
    // index a reader can act on. Atom `i` is not record `i` once a header exists.
    let mut records = Vec::with_capacity(atoms.len());
    let mut record = 0usize;
    for atom in &atoms {
        records.push(record);
        record += match atom {
            LeanAtom::Term(_) => 1,
            LeanAtom::Group { members, .. } => 1 + members.len(),
        };
    }
    let indices: Vec<usize> = (0..atoms.len()).collect();
    let mut acc_c0 = Ext::ZERO;
    let mut acc_c2 = Ext::ZERO;
    for (list, list_atoms) in split_round_robin(&indices, k).iter().enumerate() {
        // §5.3: ONE partial carries the seed. `k` seeded partials would reduce to
        // `k * c_init`.
        let mut partial_c0 = if list == 0 { seed } else { Ext::ZERO };
        let mut partial_c2 = Ext::ZERO;
        for &index in list_atoms {
            match &atoms[index] {
                LeanAtom::Term(term) => lean_record(
                    layer,
                    records[index],
                    term,
                    row,
                    resolver,
                    &mut partial_c0,
                    &mut partial_c2,
                )?,
                LeanAtom::Group {
                    core,
                    has_c0,
                    has_c2,
                    members,
                } => lean_group(
                    layer,
                    records[index],
                    GroupHeader {
                        core: *core,
                        has_c0: *has_c0,
                        has_c2: *has_c2,
                    },
                    members,
                    row,
                    resolver,
                    &mut partial_c0,
                    &mut partial_c2,
                )?,
            }
        }
        acc_c0.add_assign(&partial_c0);
        acc_c2.add_assign(&partial_c2);
    }
    Ok((acc_c0, acc_c2))
}

/// The per-side products one record's CLASS contributes, with its COEFFICIENT
/// factored out — the one place the wire's projection paths are spelled, so a plain
/// record and a group member cannot read their operands differently (§4.1: grouping
/// changes which factor multiplies the products, never the products).
enum LeanParts {
    /// `acc_c0 += <coefficient> * v`.
    C0(Ext),
    /// `acc_c2 += <coefficient> * v`.
    C2(Ext),
    /// Both sides, from one source-pair resolution per operand.
    Dual { c0: Ext, c2: Ext },
}

/// The projections `category` consumes at `row`, resolved.
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
fn lean_parts(
    layer: &CoeffLayer,
    category: TermCategory,
    position: usize,
    record: &LeanTerm,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<LeanParts, LeanInterpError> {
    let a = SourceId(u32::from(record.source_a));
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => {
            let (e0, _) = source_pair(layer, a, row, resolver)?;
            Ok(LeanParts::C0(e0))
        }
        TermCategory::C2ProductBfBf | TermCategory::C2ProductBfE4 | TermCategory::C2ProductE4E4 => {
            let b = second_source(position, record)?;
            let (_, da) = source_pair(layer, a, row, resolver)?;
            let (_, db) = source_pair(layer, b, row, resolver)?;
            let mut v = da;
            v.mul_assign(&db);
            Ok(LeanParts::C2(v))
        }
        TermCategory::DualProductE4 => {
            let b = second_source(position, record)?;
            let (a0, ad) = source_pair(layer, a, row, resolver)?;
            let (b0, bd) = source_pair(layer, b, row, resolver)?;
            let mut c0 = a0;
            c0.mul_assign(&b0);
            let mut c2 = ad;
            c2.mul_assign(&bd);
            Ok(LeanParts::Dual { c0, c2 })
        }
        // The lean class tables carry no `Move` row — `lean.rs`'s
        // `is_densified_frozen_table` proves it when the crate compiles — so
        // `lean_category` cannot return one.
        TermCategory::MoveBf | TermCategory::MoveE4 => {
            unreachable!("the lean class tables have no move rows")
        }
    }
}

/// The category `record`'s class names in `regime`, rejecting a dead class by the
/// record's POSITION in the program.
fn record_category(
    regime: crate::BwdRegime,
    position: usize,
    record: &LeanTerm,
) -> Result<TermCategory, LeanCodecError> {
    let class = u16::from(record.class);
    lean_category(regime, class).ok_or(LeanCodecError::ClassNotInRegime {
        term: position,
        opcode: class,
    })
}

/// Add one decoded PLAIN record's contribution to its list's partial pair: its own
/// coefficient times the products its class contributes.
///
/// A grouped member never comes here — its `coeff` field is an [`ImmediateId`], not
/// a [`CoefficientRecipeId`], so resolving it as a recipe would read the wrong id
/// space entirely. Members go through [`lean_group`], which is the only caller that
/// decodes that field as an immediate.
fn lean_record(
    layer: &CoeffLayer,
    position: usize,
    record: &LeanTerm,
    row: usize,
    resolver: &impl CoeffResolver,
    acc_c0: &mut Ext,
    acc_c2: &mut Ext,
) -> Result<(), LeanInterpError> {
    let category = record_category(layer.regime, position, record)?;
    let k = coefficient(
        layer,
        CoefficientRecipeId(u32::from(record.coeff)),
        resolver,
    )?;
    match lean_parts(layer, category, position, record, row, resolver)? {
        LeanParts::C0(v) => {
            let mut t = k;
            t.mul_assign(&v);
            acc_c0.add_assign(&t);
        }
        LeanParts::C2(v) => {
            let mut t = k;
            t.mul_assign(&v);
            acc_c2.add_assign(&t);
        }
        LeanParts::Dual { c0, c2 } => {
            let mut t0 = k;
            t0.mul_assign(&c0);
            acc_c0.add_assign(&t0);
            let mut t2 = k;
            t2.mul_assign(&c2);
            acc_c2.add_assign(&t2);
        }
    }
    Ok(())
}

/// A decoded group header's three scalar fields, so [`lean_group`] does not take
/// three positional arguments that are all `u16`/`bool`.
struct GroupHeader {
    core: u16,
    has_c0: bool,
    has_c2: bool,
}

/// Add one decoded GROUP atom's contribution to its list's partial pair:
/// `core * SUM_m imm_m * v_m`, per side (§4.1).
///
/// This is [`interpret_coeff_layer`]'s group loop over wire records instead of
/// `CoeffTerm`s: the members' products come from the SAME [`lean_parts`] a plain
/// record uses, the per-member immediate goes through the SAME
/// [`immediate_value`] / [`accumulate_imm`] pair the semantic interpreter uses (so
/// `±1` costs no multiplication there either), and the core multiplies each side
/// exactly once — and is skipped outright on a side the flags say the group does
/// not feed, rather than multiplied against zero.
///
/// The header's `core` is read as a bank id in the ordinary recipe id space, so a
/// core that is a reserved literal would evaluate as that literal instead of being
/// rejected: `GroupCoreIsLiteral` is [`lean::validate_program`]'s statement about a
/// stream, not a step this evaluation needs (the value would still be the layer's).
fn lean_group(
    layer: &CoeffLayer,
    header: usize,
    group: GroupHeader,
    members: &[LeanTerm],
    row: usize,
    resolver: &impl CoeffResolver,
    acc_c0: &mut Ext,
    acc_c2: &mut Ext,
) -> Result<(), LeanInterpError> {
    let core = coefficient(layer, CoefficientRecipeId(u32::from(group.core)), resolver)?;
    let mut s_c0 = Ext::ZERO;
    let mut s_c2 = Ext::ZERO;
    for (offset, member) in members.iter().enumerate() {
        // Members occupy the records right after their header, so this is the
        // member's own position in the program.
        let position = header + 1 + offset;
        let category = record_category(layer.regime, position, member)?;
        let id = ImmediateId(member.coeff);
        let imm = immediate_value(layer, id)?;
        match lean_parts(layer, category, position, member, row, resolver)? {
            LeanParts::C0(v) => accumulate_imm(&mut s_c0, id, imm, v),
            LeanParts::C2(v) => accumulate_imm(&mut s_c2, id, imm, v),
            LeanParts::Dual { c0, c2 } => {
                accumulate_imm(&mut s_c0, id, imm, c0);
                accumulate_imm(&mut s_c2, id, imm, c2);
            }
        }
    }
    if group.has_c0 {
        let mut v = core;
        v.mul_assign(&s_c0);
        acc_c0.add_assign(&v);
    }
    if group.has_c2 {
        let mut v = core;
        v.mul_assign(&s_c2);
        acc_c2.add_assign(&v);
    }
    Ok(())
}

/// The category a lean class names in `regime`, or `None` for a dead class.
///
/// The tables are the wire ABI and are public, so this and
/// [`lean::validate_program`] read the same rows; only the `find` is spelled
/// twice.
fn lean_category(regime: crate::BwdRegime, class: u16) -> Option<TermCategory> {
    let table = match regime {
        crate::BwdRegime::R0 => LEAN_R0_OPCODES,
        crate::BwdRegime::Ext => LEAN_CONT_OPCODES,
    };
    table
        .iter()
        .find(|(listed, _)| *listed == class)
        .map(|(_, category)| *category)
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
