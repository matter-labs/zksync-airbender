//! Fixed-width backward term encoding.
//!
//! ```text
//! word0 = [class:3 @13 | coeff_idx:13 @0]
//! word1 = source_a           (slot into CoeffLayer::sources)
//! word2 = source_b           (slot, or SOURCE_NONE for a one-source class)
//! ```
//!
//! Continuation groups use one control record followed by their members:
//!
//! ```text
//! word0 = [class = LEAN_CONT_GROUP_HEADER_CLASS (2) @13 | core coeff_idx:13 @0]
//! word1 = member count N (>= 2)
//! word2 = flags: bit0 = has_c0, bit1 = has_c2 (at least one set)
//! ```
//!
//! Member coefficient fields are [`ImmediateId`] values; singleton and header
//! fields are recipe ids. Class `2` is an R0 term and a continuation header, so
//! decoding requires the regime.

use gkr_eval_ir::FieldKind;

use super::limits::{
    category_arity, term_category, TermCategory, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS,
    LEAN_CONT_GROUP_HEADER_CLASS, MAX_OPCODES_PER_REGIME,
};
use super::model::{
    CoeffGroup, CoeffLayer, CoeffTerm, CoefficientRecipeId, ImmediateId, SourceId, TermId,
};

// ── Wire geometry ────────────────────────────────────────────────────────────

/// u16 words one term record occupies. Fixed: see the module doc.
pub const LEAN_WORDS_PER_TERM: usize = 3;
/// Bytes one term record occupies — what the descriptor budget is sized from.
pub(crate) const LEAN_BYTES_PER_TERM: usize = 2 * LEAN_WORDS_PER_TERM;

/// `word0` bits 0..12: the [`CoefficientRecipeId`], reserved literals included.
pub const LEAN_COEFFICIENT_SHIFT: u32 = 0;
/// Mask of [`LEAN_COEFFICIENT_SHIFT`], pre-shift.
pub(crate) const LEAN_COEFFICIENT_MASK: u16 = (1 << HEADER_COEFFICIENT_BITS) - 1;
/// `word0` bits 13..15: the class.
pub const LEAN_CLASS_SHIFT: u32 = HEADER_COEFFICIENT_BITS;
/// Mask of [`LEAN_CLASS_SHIFT`], pre-shift.
pub(crate) const LEAN_CLASS_MASK: u16 = (1 << HEADER_OPCODE_BITS) - 1;

/// `source_b` of a one-source class. Never a slot: a source table long enough to
/// reach it is unrepresentable on this wire and [`encode_program`] rejects one
/// (the corpus maximum is 1,062 sources).
pub const SOURCE_NONE: u16 = 0xFFFF;

/// A group header's `word2` bit 0: the group's core multiplies into `acc_c0`.
pub const LEAN_GROUP_FLAG_C0: u16 = 1;
/// A group header's `word2` bit 1: the group's core multiplies into `acc_c2`.
pub const LEAN_GROUP_FLAG_C2: u16 = 2;
/// The only bits `word2` admits — anything else is a malformed header.
pub(crate) const LEAN_GROUP_FLAG_MASK: u16 = LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2;

const _: () = assert!(LEAN_CLASS_SHIFT == 13);
const _: () = assert!(LEAN_CONT_GROUP_HEADER_CLASS <= LEAN_CLASS_MASK);
const _: () = assert!(LEAN_COEFFICIENT_MASK == 0x1fff);
const _: () = assert!(LEAN_CLASS_MASK as usize == MAX_OPCODES_PER_REGIME - 1);
const _: () = assert!(LEAN_BYTES_PER_TERM == 6);

// ── Lean class tables ────────────────────────────────────────────────────────
//
// The CUDA side mirrors these class numbers with static assertions.

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
pub const LEAN_CONT_OPCODES: &[(u16, TermCategory)] = &[
    (0, TermCategory::C0LinearE4),
    (1, TermCategory::DualProductE4),
];

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

const _: () = assert!(LEAN_R0_OPCODES.len() == 5);
const _: () = assert!(LEAN_CONT_OPCODES.len() == 2);
const _: () = assert!(table_is_canonical(LEAN_R0_OPCODES));
const _: () = assert!(table_is_canonical(LEAN_CONT_OPCODES));

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
const _: () = assert!(class_is_free(
    LEAN_CONT_OPCODES,
    LEAN_CONT_GROUP_HEADER_CLASS
));
const _: () = assert!(!class_is_free(
    LEAN_R0_OPCODES,
    LEAN_CONT_GROUP_HEADER_CLASS
));

/// The lean class table of one regime.
const fn lean_table(regime: crate::BwdRegime) -> &'static [(u16, TermCategory)] {
    match regime {
        crate::BwdRegime::R0 => LEAN_R0_OPCODES,
        crate::BwdRegime::Ext => LEAN_CONT_OPCODES,
    }
}

/// The class of `category` in `regime`, or `None` when the regime does not admit
/// the category at all.
fn lean_class(regime: crate::BwdRegime, category: TermCategory) -> Option<u16> {
    lean_table(regime)
        .iter()
        .find(|(_, listed)| *listed == category)
        .map(|(class, _)| *class)
}

/// The category a class names in `regime`, or `None` for a dead class.
fn lean_category(regime: crate::BwdRegime, class: u16) -> Option<TermCategory> {
    lean_table(regime)
        .iter()
        .find(|(listed, _)| *listed == class)
        .map(|(_, category)| *category)
}

// ── Program and records ──────────────────────────────────────────────────────

/// One encoded lean program in committed order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanProgram {
    pub words: Vec<u16>,
    pub term_count: usize,
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
pub(crate) enum LeanAtomRef {
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
/// included, so `3 · index` is the offending record's word offset — with the one
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
    /// The stream is not whole fixed-width records.
    TruncatedStream { words: usize },
    /// A group header claims `members` records but the stream ends first (`Ext`).
    TruncatedGroup { atom: usize, members: usize },
    /// A group header claims fewer than two members. A one-member group is not a
    /// group: it would spend a core multiply to save nothing.
    GroupMemberCountInvalid { atom: usize, members: usize },
    /// A group header's `word2` is zero (a core that multiplies into neither
    /// accumulator) or sets a bit outside [`LEAN_GROUP_FLAG_MASK`]. Words-only, so
    /// the DECODER rejects it; the cross-check against the members is
    /// [`LeanCodecError::GroupFlagsMismatch`].
    GroupFlagsInvalid { atom: usize, flags: u16 },
    /// A group header's flags disagree with the accumulator sides its member
    /// classes actually touch. Needs the class table, so the VALIDATOR rejects it.
    GroupFlagsMismatch {
        atom: usize,
        flags: u16,
        expected: u16,
    },
    /// A member record carries the group-header control code. Groups do not nest.
    NestedGroupHeader { atom: usize, member: usize },
    /// A group header's core id is a reserved literal.
    GroupCoreIsLiteral { atom: usize },
    /// A member's immediate id addresses neither `±1` nor a
    /// `CoeffLayer::immediates` entry.
    ImmediateOutOfRange { term: usize, id: u16 },
    /// A group member's coefficient is not the group's core id.
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
pub(crate) fn encode_program(
    layer: &CoeffLayer,
    order: &[TermId],
) -> Result<LeanProgram, LeanCodecError> {
    let mut words = Vec::with_capacity(order.len() * LEAN_WORDS_PER_TERM);
    for (index, id) in order.iter().enumerate() {
        let term = &layer.terms[id.0 as usize];
        let coeff = CoeffField::Recipe(term.coefficient());
        encode_term(&mut words, layer, index, term, coeff)?;
    }
    Ok(LeanProgram {
        words,
        term_count: layer.terms.len(),
    })
}

/// Encode plain terms and grouped atoms in their committed order.
///
/// # Panics
///
/// If an atom names a term outside `layer.terms` or a group outside `layer.groups`.
pub(crate) fn encode_program_atoms(
    layer: &CoeffLayer,
    atoms: &[LeanAtomRef],
) -> Result<LeanProgram, LeanCodecError> {
    let mut words = Vec::with_capacity(atoms.len() * LEAN_WORDS_PER_TERM);
    let mut record = 0usize;
    for atom in atoms {
        match atom {
            LeanAtomRef::Term(id) => {
                let term = &layer.terms[id.0 as usize];
                let coeff = CoeffField::Recipe(term.coefficient());
                encode_term(&mut words, layer, record, term, coeff)?;
                record += 1;
            }
            LeanAtomRef::Group(index) => {
                let group = &layer.groups[*index];
                encode_group(&mut words, layer, record, group)?;
                record += 1 + group.members.len();
            }
        }
    }
    Ok(LeanProgram {
        words,
        term_count: layer.terms.len(),
    })
}

/// Append one group header followed by its members.
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
        return Err(LeanCodecError::GroupMemberCountInvalid {
            atom: record,
            members,
        });
    }
    let flags = u16::from(group.has_c0) | (u16::from(group.has_c2) << 1);
    if flags == 0 {
        return Err(LeanCodecError::GroupFlagsInvalid {
            atom: record,
            flags,
        });
    }
    words.push((LEAN_CONT_GROUP_HEADER_CLASS << LEAN_CLASS_SHIFT) | core);
    // A group's members are distinct terms of one layer, and a layer's record
    // count is bounded far inside a u16 by the program caps — a member count that
    // does not fit is a broken transform.
    words.push(u16::try_from(members).expect("a group's member count fits the header word"));
    words.push(flags);
    for (offset, member) in group.members.iter().enumerate() {
        let position = record + 1 + offset;
        let term = &layer.terms[member.term.0 as usize];
        if term.coefficient() != group.core {
            return Err(LeanCodecError::MemberCoefficientNotCore {
                atom: record,
                term: member.term.0 as usize,
            });
        }
        encode_term(
            words,
            layer,
            position,
            term,
            CoeffField::Immediate(member.immediate),
        )?;
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

/// Append one term record, checking exactly what the pre-group encoder
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
/// A mixed `C2Product` is normalized to BF-first. `C2ProductBF_E4` covers both
/// field orders, so the class alone
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
        CoeffTerm::C2Product {
            lhs,
            rhs,
            lhs_field,
            rhs_field,
            ..
        } => {
            let transposed = matches!((lhs_field, rhs_field), (FieldKind::Ext, FieldKind::Base));
            let (first, second) = if transposed { (rhs, lhs) } else { (lhs, rhs) };
            Ok((slot(first.source)?, slot(second.source)?))
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => Ok((slot(*lhs)?, slot(*rhs)?)),
    }
}

// ── Decoding and validation ──────────────────────────────────────────────────

/// Unpack the whole stream into ATOMS. Bank-free and table-free: it checks the
/// stream's structure and, in `Ext`, everything a
/// self-delimiting walk needs to be unambiguous (`N >= 2`, well-formed flags, no
/// nesting, no truncated group, the declared term total) — and reads the fields.
/// [`validate_program`] is what decides legality against a layer.
///
/// `regime` is not a preference: class `2` is a live R0 term class and the `Ext`
/// group-header control code, and no property of the words distinguishes them.
pub(crate) fn decode_atoms(
    program: &LeanProgram,
    regime: crate::BwdRegime,
) -> Result<Vec<LeanAtom>, LeanCodecError> {
    match regime {
        crate::BwdRegime::R0 => decode_r0_atoms(program),
        crate::BwdRegime::Ext => decode_ext_atoms(program),
    }
}

/// R0 has no headers, so every record is a term.
fn decode_r0_atoms(program: &LeanProgram) -> Result<Vec<LeanAtom>, LeanCodecError> {
    if !program.words.len().is_multiple_of(LEAN_WORDS_PER_TERM) {
        return Err(LeanCodecError::TruncatedStream {
            words: program.words.len(),
        });
    }
    let mut out = Vec::with_capacity(program.words.len() / LEAN_WORDS_PER_TERM);
    for record in program.words.as_chunks::<LEAN_WORDS_PER_TERM>().0 {
        out.push(LeanAtom::Term(term_record(record)));
    }
    Ok(out)
}

/// Decode the self-delimiting continuation stream.
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
    let mut index = 0usize;
    while index < records {
        let record = at(index);
        if record_class(record) != LEAN_CONT_GROUP_HEADER_CLASS {
            atoms.push(LeanAtom::Term(term_record(record)));
            index += 1;
            continue;
        }
        let core = record_coefficient(record);
        let members = usize::from(record[1]);
        let flags = record[2];
        if members < 2 {
            return Err(LeanCodecError::GroupMemberCountInvalid {
                atom: index,
                members,
            });
        }
        if flags == 0 || flags & !LEAN_GROUP_FLAG_MASK != 0 {
            return Err(LeanCodecError::GroupFlagsInvalid { atom: index, flags });
        }
        if records - index - 1 < members {
            return Err(LeanCodecError::TruncatedGroup {
                atom: index,
                members,
            });
        }
        let mut decoded = Vec::with_capacity(members);
        for offset in 1..=members {
            let member = at(index + offset);
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
        index += 1 + members;
    }
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

/// Read one record as a term.
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
/// decoder's output for an R0 or group-free stream.
///
/// A member's [`LeanTerm::coeff`] is an [`ImmediateId`] and its group's core is not
/// in the returned list, so this is the right view for a consumer that cares about
/// CLASSES and SOURCES (the class-coverage walks, the deal's record census) and the
/// wrong one for a consumer that must evaluate coefficients — that one wants
/// [`decode_atoms`].
pub(crate) fn validate_program(
    program: &LeanProgram,
    layer: &CoeffLayer,
) -> Result<(), LeanCodecError> {
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
            LeanAtom::Group {
                core,
                has_c0,
                has_c2,
                members,
            } => {
                debug_assert_eq!(
                    layer.regime,
                    crate::BwdRegime::Ext,
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
    lean_category(layer.regime, class).ok_or(LeanCodecError::ClassNotInRegime {
        term: record,
        opcode: class,
    })
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
        return Err(LeanCodecError::SourceOutOfRange {
            term: record,
            slot: decoded.source_a,
        });
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
            return Err(LeanCodecError::SourceOutOfRange {
                term: record,
                slot: decoded.source_b,
            });
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
        TermCategory::C2ProductBfBf | TermCategory::C2ProductBfE4 | TermCategory::C2ProductE4E4 => {
            LEAN_GROUP_FLAG_C2
        }
        TermCategory::DualProductE4 => LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2,
    }
}

// ── Disassembly ──────────────────────────────────────────────────────────────
