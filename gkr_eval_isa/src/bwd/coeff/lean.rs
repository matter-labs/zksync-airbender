//! The LEAN term wire (segmented-lean-VM design §4): one fixed 8-byte,
//! header-first record per coefficient term, and nothing else.
//!
//! # The only backward wire
//!
//! The retired cell-era codec encoded source windows, first-access bits, residency
//! modes, fill/plan extension words and standalone `Move` opcodes. The segmented
//! lean VM has no resident state and no cell file, so none of those fields had a
//! meaning it could carry — this was never a variant of that format but a
//! different one, and since that lineage was deleted it is the ONLY backward term
//! wire. Its neighbours are [`lean_bind`](super::lean_bind) (the placement-free
//! per-source binding) and [`lean_artifact`](super::lean_artifact) (the per-layer
//! coordinate); the opcode NUMBERING it densifies still lives in
//! [`limits`](super::limits), which is what `is_densified_frozen_table` below
//! checks it against.
//!
//! # The record (v2)
//!
//! ```text
//! word0 = [class:3 @13 | coeff_idx:13 @0]
//! word1 = source_a           (slot into CoeffLayer::sources)
//! word2 = source_b           (slot, or SOURCE_NONE for a one-source class)
//! word3 = 0                  (reserved, validator-enforced)
//! ```
//!
//! HEADER-FIRST because each warp walks its own contiguous term list strictly
//! sequentially: an operand-first record is not self-delimiting for a sequential
//! decoder, so the class has to arrive before the words whose count it fixes.
//! The width is FIXED at four words even though the class already fixes the
//! source count, which keeps a term's address a shift and makes the
//! round-robin `K`-split of the word stream positional.
//!
//! The class implies the PROJECTION each source is read at — `C0Linear`
//! `Endpoint0`, `C2Product` `Delta`, `DualProduct` both — so no projection is on
//! the wire; the IR's own invariant (`CoeffTerm::C0Linear::value` is always an
//! `Endpoint0`, a `C2Product`'s operands always `Delta`) is what supplies it.
//! `source_a == source_b` is simply legal: with no resident state there is no
//! double-write hazard for a squared product.
//!
//! # Group header records (`Ext` only, design §4.4)
//!
//! A coefficient GROUP ([`CoeffGroup`]) travels as one CONTROL record followed by
//! its member term records:
//!
//! ```text
//! word0 = [class = LEAN_CONT_GROUP_HEADER_CLASS (2) @13 | core coeff_idx:13 @0]
//! word1 = member count N (>= 2)
//! word2 = flags: bit0 = has_c0, bit1 = has_c2 (at least one set)
//! word3 = 0                  (reserved, decoder-enforced)
//! ```
//!
//! The header is a CONTROL code, not a term class: the frozen class tables above
//! stay term-only, and a decoder branches on `class == 2` BEFORE any category
//! lookup. The N records that follow are ordinary term records except that their
//! thirteen coefficient bits are an [`ImmediateId`] (`0` -> `+1`, `1` -> `-1`,
//! `id >= 2` -> `CoeffLayer::immediates[id - 2]`) instead of a recipe id. Outside a
//! group the field keeps its recipe meaning, so a SINGLETON record is byte-identical
//! to what this codec emitted before groups existed.
//!
//! Two consequences the whole module is shaped by:
//!
//!   * **Decode needs the regime.** Class `2` is a LIVE R0 term class
//!     (`C2ProductBfBf`) and an `Ext` control code, and the words cannot tell them
//!     apart — [`decode_atoms`] / [`decode_program`] take a [`BwdRegime`], and the
//!     R0 path is behaviourally identical to the regime-free one it replaced.
//!   * **`term_count` stays SEMANTIC.** It counts TERMS (`order.len()`), never
//!     records, so R0 keeps its one legal stream length while `Ext` becomes a
//!     self-delimiting walk that checks `Σ members + singletons == term_count`;
//!     `words.len() == 4 · (term_count + headers)` then follows from the walk having
//!     consumed the stream exactly.
//!
//! # What is deliberately NOT here
//!
//! No cells, lanes, windows, columns, residency modes, fill or plan words, no
//! `Move` opcodes, no `first_access`, no extension words, no per-source class
//! (those are per-`(source, round)` and are assigned at GPU round lowering, not
//! stored in the `K`-free artifact model). The `K`-split itself is
//! [`order::split_round_robin`](super::order::split_round_robin) and is not a
//! codec concern: a program is one list of terms in the committed order.

use std::fmt::Write as _;

use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind};
use serde::{Deserialize, Serialize};

use super::limits::{
    CONTINUATION_OPCODE_TABLE, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS,
    LEAN_CONT_GROUP_HEADER_CLASS, MAX_OPCODES_PER_REGIME, R0_OPCODE_TABLE, TermCategory,
    category_arity, is_move, term_category,
};
use super::model::{
    CoeffGroup, CoeffLayer, CoeffTerm, CoefficientRecipeId, ImmediateId, SourceId, TermId,
};

// ── Wire geometry ────────────────────────────────────────────────────────────

/// u16 words one term record occupies. Fixed: see the module doc.
pub const LEAN_WORDS_PER_TERM: usize = 4;
/// Bytes one term record occupies — what the descriptor budget is sized from.
pub const LEAN_BYTES_PER_TERM: usize = 2 * LEAN_WORDS_PER_TERM;

/// `word0` bits 0..12: the [`CoefficientRecipeId`], reserved literals included.
pub const LEAN_COEFFICIENT_SHIFT: u32 = 0;
/// Mask of [`LEAN_COEFFICIENT_SHIFT`], pre-shift.
pub const LEAN_COEFFICIENT_MASK: u16 = (1 << HEADER_COEFFICIENT_BITS) - 1;
/// `word0` bits 13..15: the class.
pub const LEAN_CLASS_SHIFT: u32 = HEADER_COEFFICIENT_BITS;
/// Mask of [`LEAN_CLASS_SHIFT`], pre-shift.
pub const LEAN_CLASS_MASK: u16 = (1 << HEADER_OPCODE_BITS) - 1;

/// `source_b` of a one-source class. Never a slot: a source table long enough to
/// reach it is unrepresentable on this wire and [`encode_program`] rejects one
/// (the corpus maximum is 1,062 sources).
pub const SOURCE_NONE: u16 = 0xFFFF;

/// A group header's `word2` bit 0: the group's core multiplies into `acc_c0`.
pub const LEAN_GROUP_FLAG_C0: u16 = 1;
/// A group header's `word2` bit 1: the group's core multiplies into `acc_c2`.
pub const LEAN_GROUP_FLAG_C2: u16 = 2;
/// The only bits `word2` admits — anything else is a malformed header.
pub const LEAN_GROUP_FLAG_MASK: u16 = LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2;

const _: () = assert!(LEAN_CLASS_SHIFT == 13);
const _: () = assert!(LEAN_CONT_GROUP_HEADER_CLASS <= LEAN_CLASS_MASK);
const _: () = assert!(LEAN_COEFFICIENT_MASK == 0x1fff);
const _: () = assert!(LEAN_CLASS_MASK as usize == MAX_OPCODES_PER_REGIME - 1);
const _: () = assert!(LEAN_BYTES_PER_TERM == 8);

// ── Lean class tables ────────────────────────────────────────────────────────
//
// The wire ABI is these NUMBERS, which the CUDA side mirrors in static
// assertions. They are the FROZEN cell-era tables minus the two `Move` forms,
// re-densified — a lean class table may not change which categories a regime
// admits, only their numbering, which `is_densified_frozen_table` enforces at
// compile time.

/// Lean R0 classes, `(class, category)`, in class order. `5..7` are invalid.
pub const LEAN_R0_OPCODES: &[(u16, TermCategory)] = &[
    (0, TermCategory::C0LinearBf),
    (1, TermCategory::C0LinearE4),
    (2, TermCategory::C2ProductBfBf),
    (3, TermCategory::C2ProductBfE4),
    (4, TermCategory::C2ProductE4E4),
];

/// Lean continuation classes, `(class, category)`, in class order. `2..7` are
/// invalid.
pub const LEAN_CONT_OPCODES: &[(u16, TermCategory)] =
    &[(0, TermCategory::C0LinearE4), (1, TermCategory::DualProductE4)];

/// Table rows are dense from zero, in order, and inside the three class bits.
const fn table_is_canonical(table: &[(u16, TermCategory)]) -> bool {
    let mut i = 0;
    while i < table.len() {
        let (class, _) = table[i];
        if class as usize != i || class as usize >= MAX_OPCODES_PER_REGIME {
            return false;
        }
        i += 1;
    }
    true
}

/// The lean table is `frozen` with the `Move` rows deleted and the rest
/// re-densified: same categories, same relative order, nothing added, nothing
/// non-`Move` dropped.
const fn is_densified_frozen_table(
    lean: &[(u16, TermCategory)],
    frozen: &[(u16, TermCategory)],
) -> bool {
    let mut i = 0;
    let mut j = 0;
    while i < lean.len() {
        while j < frozen.len() && frozen[j].1.tag() != lean[i].1.tag() {
            if !is_move(frozen[j].1) {
                return false;
            }
            j += 1;
        }
        if j == frozen.len() {
            return false;
        }
        i += 1;
        j += 1;
    }
    while j < frozen.len() {
        if !is_move(frozen[j].1) {
            return false;
        }
        j += 1;
    }
    true
}

const _: () = assert!(LEAN_R0_OPCODES.len() == 5);
const _: () = assert!(LEAN_CONT_OPCODES.len() == 2);
const _: () = assert!(table_is_canonical(LEAN_R0_OPCODES));
const _: () = assert!(table_is_canonical(LEAN_CONT_OPCODES));
const _: () = assert!(is_densified_frozen_table(LEAN_R0_OPCODES, R0_OPCODE_TABLE));
const _: () = assert!(is_densified_frozen_table(LEAN_CONT_OPCODES, CONTINUATION_OPCODE_TABLE));

/// No row of `table` numbers `class`.
const fn class_is_free(table: &[(u16, TermCategory)], class: u16) -> bool {
    let mut i = 0;
    while i < table.len() {
        if table[i].0 == class {
            return false;
        }
        i += 1;
    }
    true
}

// The group header is a CONTROL code, so it may not collide with a live
// continuation TERM class — the one fence that keeps `decode_atoms`' `class == 2`
// branch unambiguous in the `Ext` regime. At R0 the same number IS a live class,
// which is exactly why decode takes a regime.
const _: () = assert!(class_is_free(LEAN_CONT_OPCODES, LEAN_CONT_GROUP_HEADER_CLASS));
const _: () = assert!(!class_is_free(LEAN_R0_OPCODES, LEAN_CONT_GROUP_HEADER_CLASS));

/// The lean class table of one regime.
const fn lean_table(regime: BwdRegime) -> &'static [(u16, TermCategory)] {
    match regime {
        BwdRegime::R0 => LEAN_R0_OPCODES,
        BwdRegime::Ext => LEAN_CONT_OPCODES,
    }
}

/// The class of `category` in `regime`, or `None` when the regime does not admit
/// the category at all.
fn lean_class(regime: BwdRegime, category: TermCategory) -> Option<u16> {
    lean_table(regime).iter().find(|(_, listed)| *listed == category).map(|(class, _)| *class)
}

/// The category a class names in `regime`, or `None` for a dead class.
fn lean_category(regime: BwdRegime, class: u16) -> Option<TermCategory> {
    lean_table(regime).iter().find(|(listed, _)| *listed == class).map(|(_, category)| *category)
}

// ── Program and records ──────────────────────────────────────────────────────

/// One encoded lean program: `term_count` fixed-width records, in the committed
/// order. `K`-free — the per-warp split is a positional function of the launch.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanProgram {
    pub words: Vec<u16>,
    pub term_count: usize,
}

impl LeanProgram {
    pub fn bytes(&self) -> usize {
        2 * self.words.len()
    }
}

/// One decoded record, exactly as the words spell it: no class table, no source
/// table and no regime are consulted, so a decoded term is not yet a valid one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeanTerm {
    pub class: u8,
    pub coeff: u16,
    pub source_a: u16,
    pub source_b: u16,
}

/// One ATOM of a committed order: a plain term, or one group of `layer.groups`.
///
/// The unit the order search ([`order`](super::order)) places and the descriptor
/// deal assigns to a warp — a group never straddles either boundary, which is why
/// the order is stated over atoms and only FLATTENED to a term permutation for the
/// artifact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LeanAtomRef {
    Term(TermId),
    /// Index into [`CoeffLayer::groups`].
    Group(usize),
}

/// One DECODED atom, exactly as the words spell it — the group counterpart of
/// [`LeanTerm`]: no class table, no bank and no immediate table are consulted, so a
/// decoded atom is not yet a valid one ([`validate_program`] decides that).
///
/// A member's [`LeanTerm::coeff`] is an [`ImmediateId`], NOT a
/// [`CoefficientRecipeId`] — the group's single recipe id is the header's `core`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanAtom {
    Term(LeanTerm),
    Group {
        /// The core recipe id, thirteen bits — never a reserved literal.
        core: u16,
        has_c0: bool,
        has_c2: bool,
        members: Vec<LeanTerm>,
    },
}

/// Everything the lean codec and its validator can reject. Every variant is
/// derivable from the inputs, and the codec's only run-time panics are
/// [`encode_program`]'s and [`encode_program_atoms`]' documented ones.
///
/// Every index a variant carries is a RECORD index in the word stream — headers
/// included, so `4 · index` is the offending record's word offset — with the one
/// documented exception of [`LeanCodecError::MemberCoefficientNotCore`], an
/// encode-side statement about the LAYER.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanCodecError {
    /// The class is not live in the layer's regime.
    ///
    /// From the validator, `opcode` is the dead wire class. From the encoder —
    /// which has no class to report, the category having none in this regime —
    /// it is the category's [`TermCategory::tag`]; `term` locates the offending
    /// term either way.
    ClassNotInRegime { term: usize, opcode: u16 },
    /// The coefficient id addresses neither a reserved literal nor a bank entry
    /// (encoder side: or does not fit the thirteen coefficient bits, in which
    /// case an id too wide for `coeff` reports `u16::MAX`).
    ///
    /// Raised for a group header's CORE id too — the core is a bank id in exactly
    /// the same id space, so the same statement covers it.
    CoefficientOutOfRange { term: usize, coeff: u16 },
    /// The slot is past `CoeffLayer::sources`.
    SourceOutOfRange { term: usize, slot: u16 },
    /// A one-source class carries a `source_b` other than [`SOURCE_NONE`].
    SourceBMustBeNone { term: usize },
    /// A two-source class carries [`SOURCE_NONE`] as its `source_b`.
    SourceBMissing { term: usize },
    /// `word3` is not the canonical zero.
    ReservedWordNonZero { term: usize },
    /// The stream is not whole fixed-width records: at R0, not exactly
    /// `term_count` of them (a fixed-width stream has ONE legal length, so a long
    /// stream is the same defect as a short one); in `Ext`, a word count that is
    /// not a multiple of [`LEAN_WORDS_PER_TERM`] at all, since there the RECORD
    /// count is derived by the walk and only the term total is declared
    /// ([`LeanCodecError::TermCountMismatch`] is the `Ext` counting reject).
    TruncatedStream { words: usize },
    /// A group header claims `members` records but the stream ends first (`Ext`).
    TruncatedGroup { atom: usize, members: usize },
    /// A group header claims fewer than two members. A one-member group is not a
    /// group: it would spend a core multiply to save nothing, and the transform
    /// never mints one (spec §4.4 `N >= 2`).
    GroupMemberCountInvalid { atom: usize, members: usize },
    /// A group header's `word2` is zero (a core that multiplies into neither
    /// accumulator) or sets a bit outside [`LEAN_GROUP_FLAG_MASK`]. Words-only, so
    /// the DECODER rejects it; the cross-check against the members is
    /// [`LeanCodecError::GroupFlagsMismatch`].
    GroupFlagsInvalid { atom: usize, flags: u16 },
    /// A group header's flags disagree with the accumulator sides its member
    /// classes actually touch. Needs the class table, so the VALIDATOR rejects it.
    GroupFlagsMismatch { atom: usize, flags: u16, expected: u16 },
    /// A member record carries the group-header control code. Groups do not nest:
    /// a group is one flat run of member records (spec §4.4).
    NestedGroupHeader { atom: usize, member: usize },
    /// A group header's core id is a reserved literal. `±1` is not a challenge
    /// core — such a term does not group at all (spec §4.1), and a literal core
    /// would mean a group whose "shared multiply" is free.
    GroupCoreIsLiteral { atom: usize },
    /// A member's immediate id addresses neither `±1` nor a
    /// `CoeffLayer::immediates` entry.
    ImmediateOutOfRange { term: usize, id: u16 },
    /// The records the `Ext` walk found carry `terms` terms, which is not the
    /// `LeanProgram::term_count` the program declares. This is the `Ext` counting
    /// invariant: `term_count` is SEMANTIC (`order.len()`), and headers are the
    /// only records it does not count.
    TermCountMismatch { terms: usize, declared: usize },
    /// A group member's own [`CoeffTerm::coefficient`] is not the group's core id
    /// (spec §4.1: the grouping transform REWRITES it, so a mismatch is a broken
    /// layer, not a broken stream).
    ///
    /// Encode-side only, and the only variant whose indices are not both record
    /// indices: `atom` is the header's record index, `term` the member's
    /// [`TermId`] — the index that addresses `layer.terms`, which is where the
    /// defect is. A decoded member record cannot be checked against this at all
    /// (no `TermId` travels on the wire), so the transform that SETS the field and
    /// the encoder that CHECKS it are the two pin points.
    MemberCoefficientNotCore { atom: usize, term: usize },
}

// ── Encoding ─────────────────────────────────────────────────────────────────

/// Encode `layer`'s terms in `order` — one record per entry, in that order.
///
/// # Panics
///
/// If `order` names a term outside `layer.terms`.
pub fn encode_program(layer: &CoeffLayer, order: &[TermId]) -> Result<LeanProgram, LeanCodecError> {
    let mut words = Vec::with_capacity(order.len() * LEAN_WORDS_PER_TERM);
    for (index, id) in order.iter().enumerate() {
        let term = &layer.terms[id.0 as usize];
        let coeff = CoeffField::Recipe(term.coefficient());
        encode_term(&mut words, layer, index, term, coeff)?;
    }
    Ok(LeanProgram { words, term_count: order.len() })
}

/// Encode `layer`'s committed ATOM order — plain records for singletons, a header
/// record plus its members for each group (spec §4.4).
///
/// The group path is `Ext`-only in production, but the function does not gate on the
/// regime: a group atom in an R0 layer would emit a header whose class collides with
/// `C2ProductBfBf`, and the transform never produces one, so there is nothing to
/// gate — R0 layers carry `groups` empty and every atom is a `Term`.
///
/// Encode-side invariants it enforces, which no decode of the words could
/// (spec §4.1): a member's own coefficient id IS its group's core, the core is not a
/// reserved literal, every member immediate addresses `layer.immediates` or `±1`, and
/// the header is one a [`decode_atoms`] of the emitted stream accepts (`N >= 2`,
/// flags non-empty).
///
/// # Panics
///
/// If an atom names a term outside `layer.terms` or a group outside `layer.groups`.
pub fn encode_program_atoms(
    layer: &CoeffLayer,
    atoms: &[LeanAtomRef],
) -> Result<LeanProgram, LeanCodecError> {
    let mut words = Vec::with_capacity(atoms.len() * LEAN_WORDS_PER_TERM);
    let mut record = 0usize;
    let mut term_count = 0usize;
    for atom in atoms {
        match atom {
            LeanAtomRef::Term(id) => {
                let term = &layer.terms[id.0 as usize];
                let coeff = CoeffField::Recipe(term.coefficient());
                encode_term(&mut words, layer, record, term, coeff)?;
                record += 1;
                term_count += 1;
            }
            LeanAtomRef::Group(index) => {
                let group = &layer.groups[*index];
                encode_group(&mut words, layer, record, group)?;
                record += 1 + group.members.len();
                term_count += group.members.len();
            }
        }
    }
    Ok(LeanProgram { words, term_count })
}

/// Append one group: the header record, then its members in the order the group
/// lists them — ascending `TermId`, which is the wire's member order (spec §4.2).
fn encode_group(
    words: &mut Vec<u16>,
    layer: &CoeffLayer,
    record: usize,
    group: &CoeffGroup,
) -> Result<(), LeanCodecError> {
    let core = coefficient_field(record, group.core)?;
    if CoefficientRecipeId(u32::from(core)).literal().is_some() {
        return Err(LeanCodecError::GroupCoreIsLiteral { atom: record });
    }
    let members = group.members.len();
    if members < 2 {
        return Err(LeanCodecError::GroupMemberCountInvalid { atom: record, members });
    }
    let flags = u16::from(group.has_c0) | (u16::from(group.has_c2) << 1);
    if flags == 0 {
        return Err(LeanCodecError::GroupFlagsInvalid { atom: record, flags });
    }
    words.push((LEAN_CONT_GROUP_HEADER_CLASS << LEAN_CLASS_SHIFT) | core);
    // The chop caps a group at `GROUP_SPLIT_MAX_MEMBERS`, three orders of magnitude
    // inside a u16, so a member count that does not fit is a broken transform.
    words.push(u16::try_from(members).expect("the chop caps a group's member count"));
    words.push(flags);
    words.push(0);
    for (offset, member) in group.members.iter().enumerate() {
        let position = record + 1 + offset;
        let term = &layer.terms[member.term.0 as usize];
        if term.coefficient() != group.core {
            return Err(LeanCodecError::MemberCoefficientNotCore {
                atom: record,
                term: member.term.0 as usize,
            });
        }
        encode_term(words, layer, position, term, CoeffField::Immediate(member.immediate))?;
    }
    Ok(())
}

/// What a record's thirteen coefficient bits MEAN — the only difference between a
/// plain record and a group member record.
#[derive(Clone, Copy)]
enum CoeffField {
    Recipe(CoefficientRecipeId),
    Immediate(ImmediateId),
}

/// Append one four-word TERM record, checking exactly what the pre-group encoder
/// checked and in the same order: the class is live in the regime, the coefficient
/// field is in range, the slots are inside the source table.
fn encode_term(
    words: &mut Vec<u16>,
    layer: &CoeffLayer,
    record: usize,
    term: &CoeffTerm,
    field: CoeffField,
) -> Result<(), LeanCodecError> {
    let category = term_category(term);
    let class = lean_class(layer.regime, category).ok_or(LeanCodecError::ClassNotInRegime {
        term: record,
        opcode: u16::from(category.tag()),
    })?;
    let coeff = match field {
        CoeffField::Recipe(id) => coefficient_field(record, id)?,
        CoeffField::Immediate(id) => immediate_field(record, layer, id)?,
    };
    let (source_a, source_b) = source_slots(record, term, layer.sources.len())?;
    words.push((class << LEAN_CLASS_SHIFT) | coeff);
    words.push(source_a);
    words.push(source_b);
    words.push(0);
    Ok(())
}

/// The header's coefficient field: the recipe id itself, thirteen bits wide.
fn coefficient_field(term: usize, id: CoefficientRecipeId) -> Result<u16, LeanCodecError> {
    let coeff = u16::try_from(id.0).unwrap_or(u16::MAX);
    if coeff > LEAN_COEFFICIENT_MASK {
        return Err(LeanCodecError::CoefficientOutOfRange { term, coeff });
    }
    Ok(coeff)
}

/// A member record's coefficient field: the [`ImmediateId`], checked against the
/// two reserved literals plus `layer.immediates` — and against the thirteen bits,
/// which the id space shares with a recipe id.
fn immediate_field(
    term: usize,
    layer: &CoeffLayer,
    id: ImmediateId,
) -> Result<u16, LeanCodecError> {
    let limit = usize::from(ImmediateId::RESERVED) + layer.immediates.len();
    if usize::from(id.0) >= limit || id.0 > LEAN_COEFFICIENT_MASK {
        return Err(LeanCodecError::ImmediateOutOfRange { term, id: id.0 });
    }
    Ok(id.0)
}

/// The two source words of one term.
///
/// A mixed `C2Product` is normalized to BF-FIRST, the same spelling the cell-era
/// wire fixes: `C2ProductBF_E4` covers both field orders, so the class alone
/// tells an executor which slot is the base-field factor only if the encoder
/// always puts it in `source_a`.
fn source_slots(
    term: usize,
    coeff_term: &CoeffTerm,
    sources: usize,
) -> Result<(u16, u16), LeanCodecError> {
    let slot = |id: SourceId| -> Result<u16, LeanCodecError> {
        let index = id.0 as usize;
        if index >= sources || index >= usize::from(SOURCE_NONE) {
            return Err(LeanCodecError::SourceOutOfRange {
                term,
                slot: u16::try_from(index).unwrap_or(SOURCE_NONE),
            });
        }
        Ok(index as u16)
    };
    match coeff_term {
        CoeffTerm::C0Linear { value, .. } => Ok((slot(value.source)?, SOURCE_NONE)),
        CoeffTerm::C2Product { lhs, rhs, lhs_field, rhs_field, .. } => {
            let transposed = matches!((lhs_field, rhs_field), (FieldKind::Ext, FieldKind::Base));
            let (first, second) = if transposed { (rhs, lhs) } else { (lhs, rhs) };
            Ok((slot(first.source)?, slot(second.source)?))
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => Ok((slot(*lhs)?, slot(*rhs)?)),
    }
}

// ── Decoding and validation ──────────────────────────────────────────────────

/// Unpack the whole stream into ATOMS. Bank-free and table-free: it checks the
/// stream's STRUCTURE — the lengths, the reserved words, and in `Ext` everything a
/// self-delimiting walk needs to be unambiguous (`N >= 2`, well-formed flags, no
/// nesting, no truncated group, the declared term total) — and reads the fields.
/// [`validate_program`] is what decides legality against a layer.
///
/// `regime` is not a preference: class `2` is a live R0 term class and the `Ext`
/// group-header control code, and no property of the words distinguishes them.
pub fn decode_atoms(
    program: &LeanProgram,
    regime: BwdRegime,
) -> Result<Vec<LeanAtom>, LeanCodecError> {
    match regime {
        BwdRegime::R0 => decode_r0_atoms(program),
        BwdRegime::Ext => decode_ext_atoms(program),
    }
}

/// R0: no headers exist, so the stream is exactly `term_count` fixed-width records
/// and every record is a term — the pre-group decoder, unchanged.
fn decode_r0_atoms(program: &LeanProgram) -> Result<Vec<LeanAtom>, LeanCodecError> {
    let expected = program.term_count.saturating_mul(LEAN_WORDS_PER_TERM);
    if program.words.len() != expected {
        return Err(LeanCodecError::TruncatedStream { words: program.words.len() });
    }
    let mut out = Vec::with_capacity(program.term_count);
    for (term, record) in program.words.chunks_exact(LEAN_WORDS_PER_TERM).enumerate() {
        if record[3] != 0 {
            return Err(LeanCodecError::ReservedWordNonZero { term });
        }
        out.push(LeanAtom::Term(term_record(record)));
    }
    Ok(out)
}

/// `Ext`: a self-delimiting walk, because a header's `N` is what fixes the record
/// count and `term_count` counts only terms (spec §4.4).
fn decode_ext_atoms(program: &LeanProgram) -> Result<Vec<LeanAtom>, LeanCodecError> {
    let words = &program.words;
    if !words.len().is_multiple_of(LEAN_WORDS_PER_TERM) {
        return Err(LeanCodecError::TruncatedStream { words: words.len() });
    }
    let records = words.len() / LEAN_WORDS_PER_TERM;
    let at = |record: usize| -> &[u16] {
        &words[record * LEAN_WORDS_PER_TERM..(record + 1) * LEAN_WORDS_PER_TERM]
    };
    let mut atoms = Vec::new();
    let mut terms = 0usize;
    let mut index = 0usize;
    while index < records {
        let record = at(index);
        if record[3] != 0 {
            return Err(LeanCodecError::ReservedWordNonZero { term: index });
        }
        if record_class(record) != LEAN_CONT_GROUP_HEADER_CLASS {
            atoms.push(LeanAtom::Term(term_record(record)));
            terms += 1;
            index += 1;
            continue;
        }
        let core = record_coefficient(record);
        let members = usize::from(record[1]);
        let flags = record[2];
        if members < 2 {
            return Err(LeanCodecError::GroupMemberCountInvalid { atom: index, members });
        }
        if flags == 0 || flags & !LEAN_GROUP_FLAG_MASK != 0 {
            return Err(LeanCodecError::GroupFlagsInvalid { atom: index, flags });
        }
        if records - index - 1 < members {
            return Err(LeanCodecError::TruncatedGroup { atom: index, members });
        }
        let mut decoded = Vec::with_capacity(members);
        for offset in 1..=members {
            let member = at(index + offset);
            if member[3] != 0 {
                return Err(LeanCodecError::ReservedWordNonZero { term: index + offset });
            }
            if record_class(member) == LEAN_CONT_GROUP_HEADER_CLASS {
                return Err(LeanCodecError::NestedGroupHeader {
                    atom: index,
                    member: index + offset,
                });
            }
            decoded.push(term_record(member));
        }
        atoms.push(LeanAtom::Group {
            core,
            has_c0: flags & LEAN_GROUP_FLAG_C0 != 0,
            has_c2: flags & LEAN_GROUP_FLAG_C2 != 0,
            members: decoded,
        });
        terms += members;
        index += 1 + members;
    }
    if terms != program.term_count {
        return Err(LeanCodecError::TermCountMismatch { terms, declared: program.term_count });
    }
    // The walk consumed the stream record by record and `terms + headers` is the
    // record count, so §4.4's `words == 4 * (term_count + headers)` holds by
    // construction rather than by a check.
    debug_assert!(words.len() >= terms * LEAN_WORDS_PER_TERM);
    Ok(atoms)
}

/// The class field of one record.
fn record_class(record: &[u16]) -> u16 {
    (record[0] >> LEAN_CLASS_SHIFT) & LEAN_CLASS_MASK
}

/// The thirteen-bit coefficient field of one record — a recipe id, or a member's
/// immediate id, or a header's core id, all in the same bits.
fn record_coefficient(record: &[u16]) -> u16 {
    (record[0] >> LEAN_COEFFICIENT_SHIFT) & LEAN_COEFFICIENT_MASK
}

/// Read one record as a term. Field-level only — the reserved word is the caller's
/// check, since only the caller knows whether the record is a term at all.
fn term_record(record: &[u16]) -> LeanTerm {
    LeanTerm {
        class: record_class(record) as u8,
        coeff: record_coefficient(record),
        source_a: record[1],
        source_b: record[2],
    }
}

/// Unpack the whole stream as a flat TERM list — [`decode_atoms`] with the group
/// headers dropped and their members spliced in place, which is exactly the
/// pre-group decoder's output for an R0 or group-free stream.
///
/// A member's [`LeanTerm::coeff`] is an [`ImmediateId`] and its group's core is not
/// in the returned list, so this is the right view for a consumer that cares about
/// CLASSES and SOURCES (the class-coverage walks, the deal's record census) and the
/// wrong one for a consumer that must evaluate coefficients — that one wants
/// [`decode_atoms`].
pub fn decode_program(
    program: &LeanProgram,
    regime: BwdRegime,
) -> Result<Vec<LeanTerm>, LeanCodecError> {
    let atoms = decode_atoms(program, regime)?;
    let mut out = Vec::with_capacity(program.term_count);
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => out.push(term),
            LeanAtom::Group { members, .. } => out.extend(members),
        }
    }
    Ok(out)
}

/// Check the stream against `layer`. The structural rules are
/// [`decode_atoms`]' (the lengths, the reserved words, and in `Ext` the group walk's
/// own rules); on top of them, per TERM record the class is live in `layer.regime`,
/// the coefficient id addresses a reserved literal or a bank entry, every slot is
/// inside `layer.sources`, and `source_b` is [`SOURCE_NONE`] exactly for the
/// one-source classes.
///
/// Per GROUP additionally: the core id addresses a BANK entry and never a literal,
/// every member's immediate id addresses `±1` or `layer.immediates`, and the
/// header's flags equal the accumulator sides its members' classes actually touch.
/// What it does NOT check is that a member's own `CoeffTerm::coefficient` is the
/// core — no `TermId` travels on the wire, so that invariant is
/// [`encode_program_atoms`]' (spec §4.1) and inventing a wire-side member↔term
/// mapping to re-check it here is exactly what this codec must not grow.
///
/// An R0 program cannot contain a header at all — [`decode_atoms`] reads class `2`
/// there as the live `C2ProductBfBf` class — so the group arm below is structurally
/// `Ext`-only, asserted rather than branched on.
///
/// What it does NOT check: that each slot's [`CoeffSource::field`] is the width
/// its class implies. A class-3 (`C2ProductBF_E4`) record whose `source_a`
/// addresses an `Ext` source passes here and is still unexecutable at that class,
/// so `Ok(())` means WELL-FORMED, not executable. Operand widths — including the
/// BF-first normalization of a mixed product a GPU executor's mixed branch
/// depends on — are an ENCODER invariant, pinned by
/// `a_mixed_product_puts_the_bf_factor_first`, not a validated one: the frozen
/// seven-variant error list has no honest home for a width rule, and reusing
/// [`LeanCodecError::ClassNotInRegime`] would misreport it as a dead class.
///
/// [`CoeffSource::field`]: super::model::CoeffSource::field
pub fn validate_program(program: &LeanProgram, layer: &CoeffLayer) -> Result<(), LeanCodecError> {
    let atoms = decode_atoms(program, layer.regime)?;
    let coefficients = CoefficientRecipeId::RESERVED as usize + layer.coefficients.len();
    let immediates = usize::from(ImmediateId::RESERVED) + layer.immediates.len();
    let mut record = 0usize;
    for atom in &atoms {
        match atom {
            LeanAtom::Term(decoded) => {
                let category = validate_class(layer, record, decoded)?;
                if usize::from(decoded.coeff) >= coefficients {
                    return Err(LeanCodecError::CoefficientOutOfRange {
                        term: record,
                        coeff: decoded.coeff,
                    });
                }
                validate_sources(layer, record, decoded, category)?;
                record += 1;
            }
            LeanAtom::Group { core, has_c0, has_c2, members } => {
                debug_assert_eq!(
                    layer.regime,
                    BwdRegime::Ext,
                    "an R0 stream decodes class 2 as a term, so it yields no group atom"
                );
                if CoefficientRecipeId(u32::from(*core)).literal().is_some() {
                    return Err(LeanCodecError::GroupCoreIsLiteral { atom: record });
                }
                if usize::from(*core) >= coefficients {
                    return Err(LeanCodecError::CoefficientOutOfRange {
                        term: record,
                        coeff: *core,
                    });
                }
                let mut expected = 0u16;
                for (offset, member) in members.iter().enumerate() {
                    let position = record + 1 + offset;
                    let category = validate_class(layer, position, member)?;
                    if usize::from(member.coeff) >= immediates {
                        return Err(LeanCodecError::ImmediateOutOfRange {
                            term: position,
                            id: member.coeff,
                        });
                    }
                    validate_sources(layer, position, member, category)?;
                    expected |= category_flags(category);
                }
                let flags = u16::from(*has_c0) | (u16::from(*has_c2) << 1);
                if flags != expected {
                    return Err(LeanCodecError::GroupFlagsMismatch {
                        atom: record,
                        flags,
                        expected,
                    });
                }
                record += 1 + members.len();
            }
        }
    }
    Ok(())
}

/// The category one record's class names in `layer.regime`, or the dead-class reject.
fn validate_class(
    layer: &CoeffLayer,
    record: usize,
    decoded: &LeanTerm,
) -> Result<TermCategory, LeanCodecError> {
    let class = u16::from(decoded.class);
    lean_category(layer.regime, class)
        .ok_or(LeanCodecError::ClassNotInRegime { term: record, opcode: class })
}

/// The slot rules of one record: inside the source table, and [`SOURCE_NONE`] in
/// `source_b` exactly for the one-source classes. Identical for a plain record and a
/// group member — a member's sources are an ordinary term's.
fn validate_sources(
    layer: &CoeffLayer,
    record: usize,
    decoded: &LeanTerm,
    category: TermCategory,
) -> Result<(), LeanCodecError> {
    if usize::from(decoded.source_a) >= layer.sources.len() {
        return Err(LeanCodecError::SourceOutOfRange { term: record, slot: decoded.source_a });
    }
    if category_arity(category) == 1 {
        if decoded.source_b != SOURCE_NONE {
            return Err(LeanCodecError::SourceBMustBeNone { term: record });
        }
    } else {
        if decoded.source_b == SOURCE_NONE {
            return Err(LeanCodecError::SourceBMissing { term: record });
        }
        if usize::from(decoded.source_b) >= layer.sources.len() {
            return Err(LeanCodecError::SourceOutOfRange { term: record, slot: decoded.source_b });
        }
    }
    Ok(())
}

/// The header flag bits one member category contributes — the wire spelling of the
/// grouping transform's own `term_sides`, which is what makes the flags a CHECKABLE
/// field rather than a hint.
fn category_flags(category: TermCategory) -> u16 {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => LEAN_GROUP_FLAG_C0,
        TermCategory::C2ProductBfBf
        | TermCategory::C2ProductBfE4
        | TermCategory::C2ProductE4E4 => LEAN_GROUP_FLAG_C2,
        TermCategory::DualProductE4 => LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2,
        // The lean class tables carry no `Move` row (`is_densified_frozen_table`
        // proves it at compile time), so `lean_category` cannot return one.
        TermCategory::MoveBf | TermCategory::MoveE4 => {
            unreachable!("the lean class tables have no move rows")
        }
    }
}

// ── Disassembly ──────────────────────────────────────────────────────────────

/// Render the program as text: a header line, then ONE line per record —
/// `word offset`, mnemonic, coefficient (`+1` / `-1` / `#bank`), then each
/// source as `s{slot}:{width}`.
///
/// A group renders as its own `group #{ordinal}  core=…  n=…  [c0|c2]` line with the
/// member records INDENTED beneath it, their coefficient column spelled `imm=`
/// because a member's thirteen bits are an [`ImmediateId`] and printing it as `k=`
/// would be a lie in exactly the place a reader is checking the format. `Ext` only:
/// at R0 class `2` is `C2ProductBfBf` and renders as the term it is.
///
/// Infallible on purpose, since a malformed program is exactly when this is
/// read: a dead class prints as `class{n}?`, a slot past the source table as
/// `s{n}:?`, a header claiming more members than the stream holds simply runs out of
/// member lines, and a length disagreement shows in the header's `terms` versus
/// `words`. The format is pinned by a test, so it cannot drift silently.
pub fn disassemble(program: &LeanProgram, layer: &CoeffLayer) -> String {
    let regime = match layer.regime {
        BwdRegime::R0 => "R0",
        BwdRegime::Ext => "Ext",
    };
    let mut out = String::new();
    let _ = writeln!(
        out,
        "; lean program regime={regime} terms={} words={} bytes={}",
        program.term_count,
        program.words.len(),
        program.bytes(),
    );
    // At R0 the record count IS the term count. In `Ext` it is the term count plus
    // the headers, and a malformed stream may not agree with either, so every whole
    // record is rendered and the count disagreement is left to the line above.
    let ext = layer.regime == BwdRegime::Ext;
    let records = program.words.chunks_exact(LEAN_WORDS_PER_TERM);
    let limit = if ext { usize::MAX } else { program.term_count };
    let mut groups = 0usize;
    let mut members_left = 0usize;
    for (index, record) in records.take(limit).enumerate() {
        let offset = index * LEAN_WORDS_PER_TERM;
        let class = record_class(record);
        if ext && members_left == 0 && class == LEAN_CONT_GROUP_HEADER_CLASS {
            let flags = record[2];
            let sides = match (flags & LEAN_GROUP_FLAG_C0 != 0, flags & LEAN_GROUP_FLAG_C2 != 0) {
                (true, true) => "[c0|c2]",
                (true, false) => "[c0]",
                (false, true) => "[c2]",
                (false, false) => "[?]",
            };
            let _ = writeln!(
                out,
                "{offset:04}  {:<14}  core={:<5} n={}  {sides}",
                format!("group #{groups}"),
                coefficient_tag(record_coefficient(record)),
                record[1],
            );
            groups += 1;
            members_left = usize::from(record[1]);
            continue;
        }
        let category = lean_category(layer.regime, class);
        let mnemonic = match category {
            Some(category) => category.label().to_string(),
            None => format!("class{class}?"),
        };
        let sources = match category {
            Some(category) => category_arity(category),
            None => 2,
        };
        let operands: Vec<String> =
            record[1..=sources].iter().map(|&slot| source_tag(layer, slot)).collect();
        let coeff = record_coefficient(record);
        if members_left > 0 {
            members_left -= 1;
            // Indent three, mnemonic thirteen: the widest lean mnemonic is exactly
            // thirteen characters, so a member line's own columns stay aligned and
            // the operand column still lands where a plain record's does.
            let _ = writeln!(
                out,
                "{offset:04}   {mnemonic:<13}  imm={:<5} {}",
                immediate_tag(coeff),
                operands.join("  |  "),
            );
        } else {
            let _ = writeln!(
                out,
                "{offset:04}  {mnemonic:<14}  k={:<5}  {}",
                coefficient_tag(coeff),
                operands.join("  |  "),
            );
        }
    }
    out
}

fn coefficient_tag(coeff: u16) -> String {
    match CoefficientRecipeId(u32::from(coeff)).bank_index() {
        None if coeff == CoefficientRecipeId::ONE.0 as u16 => "+1".to_string(),
        None => "-1".to_string(),
        Some(index) => format!("#{index}"),
    }
}

/// A member's coefficient field, in the id space §4.4 gives it.
fn immediate_tag(id: u16) -> String {
    match ImmediateId(id).bank_index() {
        None if id == ImmediateId::ONE.0 => "+1".to_string(),
        None => "-1".to_string(),
        Some(index) => format!("#{index}"),
    }
}

fn source_tag(layer: &CoeffLayer, slot: u16) -> String {
    if slot == SOURCE_NONE {
        return "none".to_string();
    }
    match layer.sources.get(usize::from(slot)) {
        Some(source) => {
            let width = match source.field {
                FieldKind::Base => "bf",
                FieldKind::Ext => "e4",
            };
            format!("s{slot}:{width}")
        }
        None => format!("s{slot}:?"),
    }
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::ReadPlace;

    use super::*;
    use crate::bwd::coeff::model::{
        CoeffGroupMember, CoeffSource, NormalizedCoefficientRecipe, ProjectionId,
    };
    use crate::bwd::coeff::order::order_terms;
    use crate::bwd::source::OriginLeaf;

    /// Bank entries the validator only COUNTS — the lean codec never reads a
    /// recipe, so the cheapest placeholder is the honest one here.
    fn bank(entries: usize) -> Vec<NormalizedCoefficientRecipe> {
        vec![NormalizedCoefficientRecipe::zero(); entries]
    }

    fn layer(
        regime: BwdRegime,
        sources: &[FieldKind],
        recipes: usize,
        terms: Vec<CoeffTerm>,
    ) -> CoeffLayer {
        CoeffLayer {
            regime,
            c_init: None,
            coefficients: bank(recipes),
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

    fn ext_layer() -> CoeffLayer {
        let terms = vec![
            c0(0, CoefficientRecipeId::ONE.0, 2, FieldKind::Ext),
            c0(1, 2, 0, FieldKind::Ext),
            dual(2, CoefficientRecipeId::NEG_ONE.0, 1, 1),
            dual(3, 3, 0, 2),
        ];
        layer(BwdRegime::Ext, &[FieldKind::Ext; 3], 2, terms)
    }

    /// Every R0 class, once.
    fn r0_layer() -> CoeffLayer {
        let terms = vec![
            c0(0, CoefficientRecipeId::ONE.0, 0, FieldKind::Base),
            c0(1, 2, 1, FieldKind::Ext),
            c2(2, 3, (0, FieldKind::Base), (0, FieldKind::Base)),
            c2(3, CoefficientRecipeId::NEG_ONE.0, (0, FieldKind::Base), (1, FieldKind::Ext)),
            c2(4, 2, (1, FieldKind::Ext), (1, FieldKind::Ext)),
        ];
        layer(BwdRegime::R0, &[FieldKind::Base, FieldKind::Ext], 2, terms)
    }

    /// The words a term should have, spelled out independently of the encoder.
    fn record(class: u16, coeff: u16, source_a: u16, source_b: u16) -> [u16; 4] {
        [(class << 13) | coeff, source_a, source_b, 0]
    }

    // ── Roundtrip ────────────────────────────────────────────────────────────

    /// Encode then decode reproduces the ORDER's terms, and the stream the
    /// encoder emits is one the validator accepts.
    #[test]
    fn roundtrip_reproduces_the_ordered_terms() {
        let layer = ext_layer();
        let order = vec![TermId(3), TermId(0), TermId(2), TermId(1)];
        let program = encode_program(&layer, &order).expect("a legal Ext layer");
        assert_eq!(program.term_count, 4);
        assert_eq!(program.words.len(), 4 * LEAN_WORDS_PER_TERM);
        assert_eq!(program.bytes(), 4 * LEAN_BYTES_PER_TERM);
        assert_eq!(validate_program(&program, &layer), Ok(()));
        assert_eq!(
            decode_program(&program, BwdRegime::Ext).expect("the encoder emits whole records"),
            vec![
                LeanTerm { class: 1, coeff: 3, source_a: 0, source_b: 2 },
                LeanTerm { class: 0, coeff: 0, source_a: 2, source_b: SOURCE_NONE },
                LeanTerm { class: 1, coeff: 1, source_a: 1, source_b: 1 },
                LeanTerm { class: 0, coeff: 2, source_a: 0, source_b: SOURCE_NONE },
            ],
        );
    }

    /// Every R0 class encodes, decodes to its own class code, and validates —
    /// against the committed order, not a hand-picked one.
    #[test]
    fn roundtrip_covers_every_r0_class() {
        let layer = r0_layer();
        let order = order_terms(&layer);
        let program = encode_program(&layer, &order).expect("a legal R0 layer");
        assert_eq!(validate_program(&program, &layer), Ok(()));
        let decoded = decode_program(&program, BwdRegime::R0).expect("whole records");
        let mut classes: Vec<u8> = decoded.iter().map(|term| term.class).collect();
        classes.sort_unstable();
        assert_eq!(classes, vec![0, 1, 2, 3, 4], "all five live R0 classes");
        for (position, term) in decoded.iter().enumerate() {
            let expected = &layer.terms[order[position].0 as usize];
            assert_eq!(
                usize::from(term.class),
                LEAN_R0_OPCODES
                    .iter()
                    .position(|(_, category)| *category == term_category(expected))
                    .expect("an R0 category"),
                "position {position} keeps the ordered term's class",
            );
            assert_eq!(u32::from(term.coeff), expected.coefficient().0);
        }
    }

    /// The record is header-first, the class occupies bits 13..15, the
    /// coefficient bits 0..12, and `word3` is the canonical zero.
    #[test]
    fn the_header_is_the_first_word() {
        let layer = ext_layer();
        let program = encode_program(&layer, &[TermId(3)]).expect("a legal term");
        assert_eq!(program.words, record(1, 3, 0, 2).to_vec());
        assert_eq!(program.words[0] >> LEAN_CLASS_SHIFT, 1, "class in the high three bits");
        assert_eq!(program.words[0] & LEAN_COEFFICIENT_MASK, 3, "coefficient in the low thirteen");
        assert_eq!(program.words[3], 0, "reserved");
    }

    /// An empty order is a legal program, not a defect.
    #[test]
    fn an_empty_order_encodes_an_empty_program() {
        let layer = ext_layer();
        let program = encode_program(&layer, &[]).expect("an empty order");
        assert_eq!(program, LeanProgram { words: Vec::new(), term_count: 0 });
        assert_eq!(validate_program(&program, &layer), Ok(()));
        assert_eq!(decode_program(&program, BwdRegime::Ext), Ok(Vec::new()));
        assert_eq!(
            disassemble(&program, &layer),
            "; lean program regime=Ext terms=0 words=0 bytes=0\n",
        );
    }

    /// A one-source class fills `source_b` with the sentinel, never with a slot.
    #[test]
    fn a_one_source_class_encodes_source_none() {
        let layer = ext_layer();
        let program = encode_program(&layer, &[TermId(0)]).expect("a legal term");
        assert_eq!(program.words[2], SOURCE_NONE);
    }

    /// `C2ProductBF_E4` covers both field orders, so the BF factor is emitted
    /// FIRST whichever operand carries it — the class cannot say which slot is
    /// base-field otherwise.
    #[test]
    fn a_mixed_product_puts_the_bf_factor_first() {
        let sources = [FieldKind::Base, FieldKind::Ext];
        let straight = layer(
            BwdRegime::R0,
            &sources,
            0,
            vec![c2(0, CoefficientRecipeId::ONE.0, (0, FieldKind::Base), (1, FieldKind::Ext))],
        );
        let transposed = layer(
            BwdRegime::R0,
            &sources,
            0,
            vec![c2(0, CoefficientRecipeId::ONE.0, (1, FieldKind::Ext), (0, FieldKind::Base))],
        );
        let expect = record(3, CoefficientRecipeId::ONE.0 as u16, 0, 1).to_vec();
        assert_eq!(encode_program(&straight, &[TermId(0)]).expect("legal").words, expect);
        assert_eq!(encode_program(&transposed, &[TermId(0)]).expect("legal").words, expect);
    }

    // ── Encoder rejections ───────────────────────────────────────────────────

    /// A category its regime does not admit: a native dual factor at R0, and a
    /// base-field `C0Linear` in the continuation regime.
    #[test]
    fn encode_rejects_a_category_the_regime_lacks() {
        let at_r0 = layer(
            BwdRegime::R0,
            &[FieldKind::Ext],
            0,
            vec![dual(0, CoefficientRecipeId::ONE.0, 0, 0)],
        );
        assert_eq!(
            encode_program(&at_r0, &[TermId(0)]),
            Err(LeanCodecError::ClassNotInRegime {
                term: 0,
                opcode: u16::from(TermCategory::DualProductE4.tag()),
            }),
        );
        let in_ext = layer(
            BwdRegime::Ext,
            &[FieldKind::Base],
            0,
            vec![c0(0, CoefficientRecipeId::ONE.0, 0, FieldKind::Base)],
        );
        assert_eq!(
            encode_program(&in_ext, &[TermId(0)]),
            Err(LeanCodecError::ClassNotInRegime {
                term: 0,
                opcode: u16::from(TermCategory::C0LinearBf.tag()),
            }),
        );
    }

    /// A coefficient id past the thirteen header bits has no encoding.
    #[test]
    fn encode_rejects_a_coefficient_past_thirteen_bits() {
        let too_wide = u32::from(LEAN_COEFFICIENT_MASK) + 1;
        let layer = layer(
            BwdRegime::Ext,
            &[FieldKind::Ext],
            too_wide as usize,
            vec![
                c0(0, CoefficientRecipeId::ONE.0, 0, FieldKind::Ext),
                c0(1, too_wide, 0, FieldKind::Ext),
            ],
        );
        assert_eq!(
            encode_program(&layer, &[TermId(0), TermId(1)]),
            Err(LeanCodecError::CoefficientOutOfRange { term: 1, coeff: too_wide as u16 }),
        );
    }

    /// A slot past the layer's own source table is a broken layer, and the
    /// encoder refuses to put it on the wire.
    #[test]
    fn encode_rejects_a_source_past_the_table() {
        let layer = layer(
            BwdRegime::Ext,
            &[FieldKind::Ext; 2],
            0,
            vec![dual(0, CoefficientRecipeId::ONE.0, 1, 9)],
        );
        assert_eq!(
            encode_program(&layer, &[TermId(0)]),
            Err(LeanCodecError::SourceOutOfRange { term: 0, slot: 9 }),
        );
    }

    // ── Validator rejections ─────────────────────────────────────────────────

    /// Classes 3..7 are dead in the continuation regime — 2 is not one of them: it
    /// is the group-header control code, and rejecting it as a dead class is exactly
    /// the confusion `decode_atoms`' header branch exists to prevent.
    #[test]
    fn validate_rejects_a_dead_class() {
        let layer = ext_layer();
        let program = LeanProgram { words: record(3, 0, 0, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::ClassNotInRegime { term: 0, opcode: 3 }),
        );
        let header = LeanProgram { words: record(2, 0, 0, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&header, &layer),
            Err(LeanCodecError::GroupMemberCountInvalid { atom: 0, members: 0 }),
            "class 2 in Ext is read as a header, malformed or not",
        );
    }

    /// The addressable coefficient ids are the two reserved literals plus the
    /// bank; one past them is out of range.
    #[test]
    fn validate_rejects_a_coefficient_past_the_bank() {
        let layer = ext_layer();
        let past = CoefficientRecipeId::RESERVED as u16 + layer.coefficients.len() as u16;
        let program =
            LeanProgram { words: record(0, past, 0, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::CoefficientOutOfRange { term: 0, coeff: past }),
        );
        let last = past - 1;
        let legal = LeanProgram { words: record(0, last, 0, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(validate_program(&legal, &layer), Ok(()), "the last bank entry is legal");
    }

    #[test]
    fn validate_rejects_a_slot_past_the_source_table() {
        let layer = ext_layer();
        let sources = layer.sources.len() as u16;
        let first =
            LeanProgram { words: record(0, 0, sources, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&first, &layer),
            Err(LeanCodecError::SourceOutOfRange { term: 0, slot: sources }),
        );
        let second = LeanProgram { words: record(1, 0, 0, sources).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&second, &layer),
            Err(LeanCodecError::SourceOutOfRange { term: 0, slot: sources }),
        );
    }

    /// A one-source class with a real slot in `source_b` would give the executor
    /// an operand its class has no factor for.
    #[test]
    fn validate_rejects_a_second_source_on_a_one_source_class() {
        let layer = ext_layer();
        let program = LeanProgram { words: record(0, 0, 1, 2).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::SourceBMustBeNone { term: 0 }),
        );
    }

    #[test]
    fn validate_rejects_a_missing_second_source() {
        let layer = ext_layer();
        let program = LeanProgram { words: record(1, 0, 1, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::SourceBMissing { term: 0 }),
        );
    }

    /// The reserved word carries no meaning, so only its canonical zero decodes.
    #[test]
    fn decode_rejects_a_nonzero_reserved_word() {
        let layer = ext_layer();
        let mut words = record(0, 0, 1, SOURCE_NONE).to_vec();
        words.extend(record(0, 0, 2, SOURCE_NONE));
        words[7] = 1;
        let program = LeanProgram { words, term_count: 2 };
        assert_eq!(
            decode_program(&program, BwdRegime::Ext),
            Err(LeanCodecError::ReservedWordNonZero { term: 1 }),
        );
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::ReservedWordNonZero { term: 1 }),
        );
    }

    /// A partial record and a trailing word are the same defect in either regime.
    /// A `term_count` that disagrees with a WHOLE-record stream is one length
    /// reject at R0 (where the record count is the term count) and the counting
    /// reject in `Ext` (where headers make the two differ by construction).
    #[test]
    fn decode_rejects_a_stream_that_is_not_whole_records() {
        let layer = ext_layer();
        let words = record(0, 0, 1, SOURCE_NONE).to_vec();
        for length in [3usize, 5] {
            let mut short = words.clone();
            short.resize(length, 0);
            let program = LeanProgram { words: short, term_count: 1 };
            assert_eq!(
                decode_program(&program, BwdRegime::Ext),
                Err(LeanCodecError::TruncatedStream { words: length }),
            );
            assert_eq!(
                validate_program(&program, &layer),
                Err(LeanCodecError::TruncatedStream { words: length }),
            );
        }
        let two_records = LeanProgram { words: words.clone(), term_count: 2 };
        assert_eq!(
            decode_program(&two_records, BwdRegime::R0),
            Err(LeanCodecError::TruncatedStream { words: 4 }),
            "at R0 term_count disagreeing with the stream is the same length defect",
        );
        assert_eq!(
            decode_program(&two_records, BwdRegime::Ext),
            Err(LeanCodecError::TermCountMismatch { terms: 1, declared: 2 }),
            "in Ext the walk counts the terms it found",
        );
    }

    // ── Group atoms (spec §4.4, §6.2) ────────────────────────────────────────

    /// A group header's four words, spelled out independently of the encoder.
    fn header(core: u16, members: u16, flags: u16) -> [u16; 4] {
        [(LEAN_CONT_GROUP_HEADER_CLASS << 13) | core, members, flags, 0]
    }

    /// Two groups and two singletons, hand-built the way the grouping transform
    /// builds one: every member's own coefficient IS its group's core (§4.1),
    /// members ascending by `TermId`, non-`±1` immediates in the layer's table.
    fn grouped_ext_layer() -> CoeffLayer {
        let core_a = CoefficientRecipeId::from_bank_index(0);
        let core_b = CoefficientRecipeId::from_bank_index(1);
        let plain = CoefficientRecipeId::from_bank_index(2);
        let terms = vec![
            c0(0, core_a.0, 0, FieldKind::Ext),
            dual(1, core_a.0, 1, 2),
            c0(2, core_b.0, 2, FieldKind::Ext),
            c0(3, core_b.0, 1, FieldKind::Ext),
            c0(4, CoefficientRecipeId::ONE.0, 0, FieldKind::Ext),
            dual(5, plain.0, 0, 1),
        ];
        let mut layer = layer(BwdRegime::Ext, &[FieldKind::Ext; 3], 3, terms);
        layer.immediates = vec![7, 9];
        layer.groups = vec![
            CoeffGroup {
                core: core_a,
                members: vec![
                    CoeffGroupMember { term: TermId(0), immediate: ImmediateId::ONE },
                    CoeffGroupMember { term: TermId(1), immediate: ImmediateId::banked(0) },
                ],
                has_c0: true,
                has_c2: true,
            },
            CoeffGroup {
                core: core_b,
                members: vec![
                    CoeffGroupMember { term: TermId(2), immediate: ImmediateId::NEG_ONE },
                    CoeffGroupMember { term: TermId(3), immediate: ImmediateId::banked(1) },
                ],
                has_c0: true,
                has_c2: false,
            },
        ];
        layer
    }

    /// The committed atom order of [`grouped_ext_layer`]: group, singleton, group,
    /// singleton — so a header is neither first nor last in the stream.
    fn grouped_atoms() -> Vec<LeanAtomRef> {
        vec![
            LeanAtomRef::Group(0),
            LeanAtomRef::Term(TermId(4)),
            LeanAtomRef::Group(1),
            LeanAtomRef::Term(TermId(5)),
        ]
    }

    fn grouped_program() -> LeanProgram {
        encode_program_atoms(&grouped_ext_layer(), &grouped_atoms())
            .expect("a legal grouped Ext layer")
    }

    /// One word of a program, replaced — how every reject below is built, so each
    /// pin has exactly ONE defect.
    fn with_word(program: &LeanProgram, word: usize, value: u16) -> LeanProgram {
        let mut mutated = program.clone();
        mutated.words[word] = value;
        mutated
    }

    /// The whole atom round trip: the encoder's words are the spelled-out wire, the
    /// decoder reproduces the atoms field for field, the validator accepts them, and
    /// `term_count` counts TERMS while the stream carries terms PLUS headers.
    #[test]
    fn atom_round_trip() {
        let layer = grouped_ext_layer();
        let program = grouped_program();
        let expected: Vec<u16> = [
            header(2, 2, LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2),
            record(0, ImmediateId::ONE.0, 0, SOURCE_NONE),
            record(1, ImmediateId::banked(0).0, 1, 2),
            record(0, CoefficientRecipeId::ONE.0 as u16, 0, SOURCE_NONE),
            header(3, 2, LEAN_GROUP_FLAG_C0),
            record(0, ImmediateId::NEG_ONE.0, 2, SOURCE_NONE),
            record(0, ImmediateId::banked(1).0, 1, SOURCE_NONE),
            record(1, 4, 0, 1),
        ]
        .concat();
        assert_eq!(program.words, expected);
        assert_eq!(program.term_count, 6, "term_count is semantic: six terms");
        assert_eq!(program.words.len(), (6 + 2) * LEAN_WORDS_PER_TERM, "six terms, two headers");
        assert_eq!(validate_program(&program, &layer), Ok(()));

        let members_a = vec![
            LeanTerm { class: 0, coeff: ImmediateId::ONE.0, source_a: 0, source_b: SOURCE_NONE },
            LeanTerm { class: 1, coeff: ImmediateId::banked(0).0, source_a: 1, source_b: 2 },
        ];
        let members_b = vec![
            LeanTerm {
                class: 0,
                coeff: ImmediateId::NEG_ONE.0,
                source_a: 2,
                source_b: SOURCE_NONE,
            },
            LeanTerm {
                class: 0,
                coeff: ImmediateId::banked(1).0,
                source_a: 1,
                source_b: SOURCE_NONE,
            },
        ];
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Ok(vec![
                LeanAtom::Group {
                    core: 2,
                    has_c0: true,
                    has_c2: true,
                    members: members_a.clone(),
                },
                LeanAtom::Term(LeanTerm {
                    class: 0,
                    coeff: 0,
                    source_a: 0,
                    source_b: SOURCE_NONE,
                }),
                LeanAtom::Group {
                    core: 3,
                    has_c0: true,
                    has_c2: false,
                    members: members_b.clone(),
                },
                LeanAtom::Term(LeanTerm { class: 1, coeff: 4, source_a: 0, source_b: 1 }),
            ]),
        );
        // The flat view splices the members in place and drops the headers, which is
        // what every class/source consumer of the wire reads.
        let mut flat = members_a;
        flat.push(LeanTerm { class: 0, coeff: 0, source_a: 0, source_b: SOURCE_NONE });
        flat.extend(members_b);
        flat.push(LeanTerm { class: 1, coeff: 4, source_a: 0, source_b: 1 });
        assert_eq!(decode_program(&program, BwdRegime::Ext), Ok(flat));
    }

    /// A group-free atom order and the term order it flattens to encode to the SAME
    /// bytes — the property that keeps every ungrouped program on the wire it is on
    /// today.
    #[test]
    fn a_group_free_atom_order_encodes_byte_identically() {
        let layer = ext_layer();
        let order = vec![TermId(3), TermId(0), TermId(2), TermId(1)];
        let atoms: Vec<LeanAtomRef> = order.iter().copied().map(LeanAtomRef::Term).collect();
        assert_eq!(encode_program_atoms(&layer, &atoms), encode_program(&layer, &order));
    }

    /// R0 decode is the pre-group decode, pinned against a hand-built stream — and
    /// class 2 there is the live `C2ProductBfBf` TERM class, which is the whole
    /// reason decode takes a regime: the same words read as a group header in `Ext`.
    #[test]
    fn r0_decode_is_byte_identical() {
        let layer = r0_layer();
        let words: Vec<u16> = [
            record(0, CoefficientRecipeId::ONE.0 as u16, 0, SOURCE_NONE),
            record(2, 2, 0, 0),
            record(4, 3, 1, 1),
        ]
        .concat();
        let program = LeanProgram { words, term_count: 3 };
        assert_eq!(
            decode_program(&program, BwdRegime::R0),
            Ok(vec![
                LeanTerm { class: 0, coeff: 0, source_a: 0, source_b: SOURCE_NONE },
                LeanTerm { class: 2, coeff: 2, source_a: 0, source_b: 0 },
                LeanTerm { class: 4, coeff: 3, source_a: 1, source_b: 1 },
            ]),
        );
        assert_eq!(validate_program(&program, &layer), Ok(()));
        let atoms = decode_atoms(&program, BwdRegime::R0).expect("three R0 records");
        assert!(
            atoms.iter().all(|atom| matches!(atom, LeanAtom::Term(_))),
            "an R0 stream has no group atom, whatever its classes",
        );
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Err(LeanCodecError::GroupMemberCountInvalid { atom: 1, members: 0 }),
            "the SAME words read as a header in Ext",
        );
    }

    /// A header claiming members the stream does not hold.
    #[test]
    fn truncated_group_rejected() {
        let words: Vec<u16> = [
            header(2, 2, LEAN_GROUP_FLAG_C0),
            record(0, ImmediateId::ONE.0, 0, SOURCE_NONE),
        ]
        .concat();
        let program = LeanProgram { words, term_count: 2 };
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Err(LeanCodecError::TruncatedGroup { atom: 0, members: 2 }),
        );
    }

    /// Groups do not nest: a member record carrying the control code is a defect,
    /// not an inner group.
    #[test]
    fn nested_header_rejected() {
        let words: Vec<u16> = [
            header(2, 2, LEAN_GROUP_FLAG_C0),
            header(3, 2, LEAN_GROUP_FLAG_C0),
            record(0, ImmediateId::ONE.0, 0, SOURCE_NONE),
        ]
        .concat();
        let program = LeanProgram { words, term_count: 2 };
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Err(LeanCodecError::NestedGroupHeader { atom: 0, member: 1 }),
        );
    }

    /// `±1` is not a challenge core, so a literal core id is rejected by BOTH sides:
    /// the validator on the words, and the encoder before it ever emits them.
    #[test]
    fn core_literal_rejected() {
        let layer = grouped_ext_layer();
        let program = with_word(
            &grouped_program(),
            0,
            (LEAN_CONT_GROUP_HEADER_CLASS << LEAN_CLASS_SHIFT) | CoefficientRecipeId::ONE.0 as u16,
        );
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext).map(|atoms| atoms.len()),
            Ok(4),
            "a literal core is well-formed on the wire",
        );
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::GroupCoreIsLiteral { atom: 0 }),
        );

        let mut literal_core = grouped_ext_layer();
        literal_core.groups[0].core = CoefficientRecipeId::NEG_ONE;
        assert_eq!(
            encode_program_atoms(&literal_core, &grouped_atoms()),
            Err(LeanCodecError::GroupCoreIsLiteral { atom: 0 }),
        );
    }

    /// The core is a bank id in the same id space a plain record's coefficient is,
    /// so one past the bank is the same statement about it.
    #[test]
    fn core_id_past_bank_rejected() {
        let layer = grouped_ext_layer();
        let past = CoefficientRecipeId::RESERVED as u16 + layer.coefficients.len() as u16;
        let program = with_word(
            &grouped_program(),
            0,
            (LEAN_CONT_GROUP_HEADER_CLASS << LEAN_CLASS_SHIFT) | past,
        );
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::CoefficientOutOfRange { term: 0, coeff: past }),
        );
    }

    /// A member's thirteen bits address `±1` plus `layer.immediates`, and one past
    /// them is out of range — reported at the MEMBER's record index.
    #[test]
    fn immediate_out_of_range_rejected() {
        let layer = grouped_ext_layer();
        let past = ImmediateId::RESERVED + layer.immediates.len() as u16;
        // Record 2 is the second member of the first group (class 1, a dual).
        let program = with_word(&grouped_program(), 2 * LEAN_WORDS_PER_TERM, (1 << 13) | past);
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::ImmediateOutOfRange { term: 2, id: past }),
        );
        let last = with_word(&grouped_program(), 2 * LEAN_WORDS_PER_TERM, (1 << 13) | (past - 1));
        assert_eq!(
            validate_program(&last, &layer),
            Ok(()),
            "the last immediate table entry is legal",
        );
        // The encoder rejects the same id before it reaches the wire.
        let mut wide = grouped_ext_layer();
        wide.groups[0].members[1].immediate = ImmediateId(past);
        assert_eq!(
            encode_program_atoms(&wide, &grouped_atoms()),
            Err(LeanCodecError::ImmediateOutOfRange { term: 2, id: past }),
        );
    }

    /// `term_count` counts TERMS, so a stream whose walk finds a different total is
    /// rejected — the `Ext` replacement for the fixed-length rule.
    #[test]
    fn term_count_mismatch_rejected() {
        let mut program = grouped_program();
        program.term_count = 5;
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Err(LeanCodecError::TermCountMismatch { terms: 6, declared: 5 }),
        );
    }

    /// A one-member group would spend a core multiply to save nothing.
    #[test]
    fn single_member_group_rejected() {
        let words: Vec<u16> = [
            header(2, 1, LEAN_GROUP_FLAG_C0),
            record(0, ImmediateId::ONE.0, 0, SOURCE_NONE),
        ]
        .concat();
        let program = LeanProgram { words, term_count: 1 };
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Err(LeanCodecError::GroupMemberCountInvalid { atom: 0, members: 1 }),
        );
        let mut single = grouped_ext_layer();
        single.groups[0].members.truncate(1);
        assert_eq!(
            encode_program_atoms(&single, &grouped_atoms()),
            Err(LeanCodecError::GroupMemberCountInvalid { atom: 0, members: 1 }),
        );
    }

    /// A core multiplying into neither accumulator, and a flag bit the format does
    /// not define, are the same words-level defect.
    #[test]
    fn flags_zero_rejected() {
        let program = with_word(&grouped_program(), 2, 0);
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext),
            Err(LeanCodecError::GroupFlagsInvalid { atom: 0, flags: 0 }),
        );
        let reserved = with_word(&grouped_program(), 2, LEAN_GROUP_FLAG_MASK + 1);
        assert_eq!(
            decode_atoms(&reserved, BwdRegime::Ext),
            Err(LeanCodecError::GroupFlagsInvalid { atom: 0, flags: LEAN_GROUP_FLAG_MASK + 1 }),
        );
        let mut sideless = grouped_ext_layer();
        sideless.groups[0].has_c0 = false;
        sideless.groups[0].has_c2 = false;
        assert_eq!(
            encode_program_atoms(&sideless, &grouped_atoms()),
            Err(LeanCodecError::GroupFlagsInvalid { atom: 0, flags: 0 }),
        );
    }

    /// Well-formed flags that do not match the sides the members' classes touch:
    /// group 0 holds a dual, so `c2` is not optional.
    #[test]
    fn flags_mismatch_members_rejected() {
        let layer = grouped_ext_layer();
        let program = with_word(&grouped_program(), 2, LEAN_GROUP_FLAG_C0);
        assert_eq!(
            decode_atoms(&program, BwdRegime::Ext).map(|atoms| atoms.len()),
            Ok(4),
            "the flags are well-formed; only the layer's classes contradict them",
        );
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::GroupFlagsMismatch {
                atom: 0,
                flags: LEAN_GROUP_FLAG_C0,
                expected: LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2,
            }),
        );
    }

    /// The grouping transform REWRITES a member's coefficient to the core, so a
    /// member that kept its own recipe id is a broken layer. No `TermId` travels on
    /// the wire, so the encoder is the only side that can say this — and it does,
    /// naming the member's `TermId` rather than a record index.
    #[test]
    fn member_coefficient_not_core_rejected() {
        let mut layer = grouped_ext_layer();
        layer.terms[1] = dual(1, CoefficientRecipeId::from_bank_index(2).0, 1, 2);
        assert_eq!(
            encode_program_atoms(&layer, &grouped_atoms()),
            Err(LeanCodecError::MemberCoefficientNotCore { atom: 0, term: 1 }),
        );
    }

    /// Every single-bit mutation of a canonical GROUPED program is rejected with a
    /// classified error, or still valid and still a consistent atom set. Never a
    /// panic and never an out-of-bounds read: the `Ext` walk does index arithmetic
    /// over a self-delimiting stream, so a header's `N` is attacker-controlled in
    /// exactly the way the R0 sweep's fixed-width records never were.
    #[test]
    fn every_single_bit_mutation_of_a_grouped_program_is_rejected_or_consistently_valid() {
        let layer = grouped_ext_layer();
        let canonical = grouped_program();
        validate_program(&canonical, &layer).expect("the canonical grouped program validates");

        let mut rejected = 0usize;
        let mut still_valid = 0usize;
        for word in 0..canonical.words.len() {
            for bit in 0..16u32 {
                let mut mutated = canonical.clone();
                mutated.words[word] ^= 1u16 << bit;
                let where_ = format!("word {word} bit {bit}");
                match validate_program(&mutated, &layer) {
                    Err(_) => {
                        rejected += 1;
                        let _ = decode_atoms(&mutated, BwdRegime::Ext);
                        let _ = decode_program(&mutated, BwdRegime::Ext);
                    }
                    Ok(()) => {
                        still_valid += 1;
                        let atoms = decode_atoms(&mutated, BwdRegime::Ext)
                            .unwrap_or_else(|e| panic!("{where_}: valid but undecodable: {e:?}"));
                        let terms: usize = atoms
                            .iter()
                            .map(|atom| match atom {
                                LeanAtom::Term(_) => 1,
                                LeanAtom::Group { members, .. } => members.len(),
                            })
                            .sum();
                        assert_eq!(terms, mutated.term_count, "{where_}: term total");
                        assert_eq!(
                            decode_program(&mutated, BwdRegime::Ext).map(|flat| flat.len()),
                            Ok(terms),
                            "{where_}: the flat view drops headers and nothing else",
                        );
                    }
                }
                // The disassembler is read exactly when a program is malformed.
                let _ = disassemble(&mutated, &layer);
            }
        }

        assert_eq!(rejected + still_valid, canonical.words.len() * 16);
        eprintln!(
            "[lean-group-mutation] {} words x 16 bits: {rejected} rejected, {still_valid} still valid",
            canonical.words.len()
        );
        assert!(rejected > 0, "no mutation was rejected");
        assert!(still_valid > 0, "no mutation stayed valid");
    }

    // ── Disassembly and serde ────────────────────────────────────────────────

    /// The pinned text format, on a legal three-term R0 program.
    #[test]
    fn disassembles_a_three_term_program() {
        let terms = vec![
            c0(0, CoefficientRecipeId::ONE.0, 2, FieldKind::Base),
            c2(1, 2, (2, FieldKind::Base), (1, FieldKind::Ext)),
            c0(2, CoefficientRecipeId::NEG_ONE.0, 1, FieldKind::Ext),
        ];
        let layer =
            layer(BwdRegime::R0, &[FieldKind::Base, FieldKind::Ext, FieldKind::Base], 1, terms);
        let order = vec![TermId(0), TermId(1), TermId(2)];
        let program = encode_program(&layer, &order).expect("a legal R0 layer");
        assert_eq!(validate_program(&program, &layer), Ok(()));
        assert_eq!(
            disassemble(&program, &layer),
            "\
; lean program regime=R0 terms=3 words=12 bytes=24
0000  C0LinearBF      k=+1     s2:bf
0004  C2ProductBF_E4  k=#0     s2:bf  |  s1:e4
0008  C0LinearE4      k=-1     s1:e4
",
        );
    }

    /// The pinned group format: one header line per group, members indented beneath
    /// it with their coefficient column spelled `imm=`.
    #[test]
    fn disassembles_a_grouped_program() {
        let layer = grouped_ext_layer();
        let program = grouped_program();
        assert_eq!(
            disassemble(&program, &layer),
            "\
; lean program regime=Ext terms=6 words=32 bytes=64
0000  group #0        core=#0    n=2  [c0|c2]
0004   C0LinearE4     imm=+1    s0:e4
0008   DualProductE4  imm=#0    s1:e4  |  s2:e4
0012  C0LinearE4      k=+1     s0:e4
0016  group #1        core=#1    n=2  [c0]
0020   C0LinearE4     imm=-1    s2:e4
0024   C0LinearE4     imm=#1    s1:e4
0028  DualProductE4   k=#2     s0:e4  |  s1:e4
",
        );
    }

    /// A dead class and a slot past the source table still render, because a
    /// malformed program is exactly what gets disassembled. Class `3` for the dead
    /// one: in `Ext`, class `2` is the group header and renders as one.
    #[test]
    fn disassembles_a_malformed_program() {
        let layer = ext_layer();
        let mut words = record(3, 0, 0, 1).to_vec();
        words.extend(record(1, 0, 9, 1));
        let program = LeanProgram { words, term_count: 2 };
        assert_eq!(
            disassemble(&program, &layer),
            "\
; lean program regime=Ext terms=2 words=8 bytes=16
0000  class3?         k=+1     s0:e4  |  s1:e4
0004  DualProductE4   k=+1     s9:?  |  s1:e4
",
        );
    }

    /// Every single-bit mutation of a canonical multi-class program is either
    /// REJECTED with a classified error, or still valid and still decodes to a
    /// well-formed record set. Never a panic, and never a record the validator
    /// accepted but the decoder disagrees about.
    ///
    /// Exhaustive per word, and cheap enough to be: fixed 8-byte records with
    /// masked fields mean the whole wire of a five-term program is 20 u16 words —
    /// 320 mutations, each a decode plus a validate. There is no length field on
    /// the wire and no variable-width record, so bit-flipping the words IS the
    /// complete malformed-input space at this level.
    ///
    /// This restores the malformed-input property the retired cell-era codec's
    /// suite carried; the lean codec had per-rule tests but nothing exhaustive.
    #[test]
    fn every_single_bit_mutation_is_rejected_or_consistently_valid() {
        let layer = r0_layer();
        let canonical = encode_program(&layer, &order_terms(&layer)).expect("a legal R0 layer");
        validate_program(&canonical, &layer).expect("the canonical program validates");

        let coefficients = CoefficientRecipeId::RESERVED as usize + layer.coefficients.len();
        let mut rejected = 0usize;
        let mut still_valid = 0usize;

        for word in 0..canonical.words.len() {
            for bit in 0..16u32 {
                let mut mutated = canonical.clone();
                mutated.words[word] ^= 1u16 << bit;
                let where_ = format!("word {word} bit {bit}");

                match validate_program(&mutated, &layer) {
                    // (a) Rejected. The error is classified by construction — the
                    // enum has no catch-all variant — so reaching here is the
                    // property. `decode_program` must agree that something is
                    // wrong OR must at least not panic.
                    Err(_) => {
                        rejected += 1;
                        // Decoding a rejected stream must still be panic-free: the
                        // disassembler is read exactly when a program is malformed.
                        let _ = decode_program(&mutated, BwdRegime::R0);
                        let _ = disassemble(&mutated, &layer);
                    }
                    // (b) Still valid. Then the decode must succeed and every
                    // record must independently satisfy the four field rules, so
                    // the validator cannot have accepted something the executor
                    // would mis-read.
                    Ok(()) => {
                        still_valid += 1;
                        let terms = decode_program(&mutated, BwdRegime::R0)
                            .unwrap_or_else(|e| panic!("{where_}: valid but undecodable: {e:?}"));
                        assert_eq!(terms.len(), layer.terms.len(), "{where_}: record count");
                        for (index, decoded) in terms.iter().enumerate() {
                            let category = lean_category(layer.regime, u16::from(decoded.class))
                                .unwrap_or_else(|| panic!("{where_}: term {index} dead class"));
                            assert!(
                                usize::from(decoded.coeff) < coefficients,
                                "{where_}: term {index} coefficient out of range"
                            );
                            assert!(
                                usize::from(decoded.source_a) < layer.sources.len(),
                                "{where_}: term {index} source_a out of range"
                            );
                            if category_arity(category) == 1 {
                                assert_eq!(
                                    decoded.source_b, SOURCE_NONE,
                                    "{where_}: term {index} unary source_b"
                                );
                            } else {
                                assert!(
                                    decoded.source_b != SOURCE_NONE
                                        && usize::from(decoded.source_b) < layer.sources.len(),
                                    "{where_}: term {index} binary source_b"
                                );
                            }
                        }
                        let _ = disassemble(&mutated, &layer);
                    }
                }
            }
        }

        assert_eq!(rejected + still_valid, canonical.words.len() * 16);
        // Both outcome classes must actually occur, or this sweep is proving only
        // one of the two properties it claims. Printed so the split is visible
        // rather than assumed: a change that collapsed one class to a handful
        // would still pass the bounds below but would mean much less.
        eprintln!(
            "[lean-mutation] {} words x 16 bits: {rejected} rejected, {still_valid} still valid",
            canonical.words.len()
        );
        assert!(rejected > 0, "no mutation was rejected");
        assert!(still_valid > 0, "no mutation stayed valid");
    }

    #[test]
    fn program_survives_a_serde_roundtrip() {
        let layer = ext_layer();
        let program = encode_program(&layer, &order_terms(&layer)).expect("a legal Ext layer");
        let json = serde_json::to_string(&program).expect("plain data");
        assert_eq!(serde_json::from_str::<LeanProgram>(&json).expect("plain data"), program);
    }
}
