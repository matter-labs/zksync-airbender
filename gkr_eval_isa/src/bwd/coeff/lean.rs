//! The LEAN term wire (segmented-lean-VM design §4): one fixed 8-byte,
//! header-first record per coefficient term, and nothing else.
//!
//! # Why a second codec
//!
//! [`encode`](super::encode) encodes the CELL-era ISA: source windows,
//! first-access bits, residency modes, fill/plan extension words, and standalone
//! `Move` opcodes. The segmented lean VM has no resident state and no cell file,
//! so none of those fields have a meaning it could carry. This module is
//! therefore not a variant of that format but a different one, and the two live
//! side by side until the cell-era lineage is retired.
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

use super::encode::{category_arity, is_move, term_category};
use super::limits::{
    CONTINUATION_OPCODE_TABLE, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS, MAX_OPCODES_PER_REGIME,
    R0_OPCODE_TABLE, TermCategory,
};
use super::model::{CoeffLayer, CoeffTerm, CoefficientRecipeId, SourceId, TermId};

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

const _: () = assert!(LEAN_CLASS_SHIFT == 13);
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

/// Everything the lean codec and its validator can reject. Every variant is
/// derivable from the inputs, and the codec's only run-time panic is
/// [`encode_program`]'s documented one.
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
    CoefficientOutOfRange { term: usize, coeff: u16 },
    /// The slot is past `CoeffLayer::sources`.
    SourceOutOfRange { term: usize, slot: u16 },
    /// A one-source class carries a `source_b` other than [`SOURCE_NONE`].
    SourceBMustBeNone { term: usize },
    /// A two-source class carries [`SOURCE_NONE`] as its `source_b`.
    SourceBMissing { term: usize },
    /// `word3` is not the canonical zero.
    ReservedWordNonZero { term: usize },
    /// The stream is not exactly `term_count` fixed-width records. A fixed-width
    /// stream has ONE legal length, so a long stream is the same defect as a
    /// short one.
    TruncatedStream { words: usize },
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
        let category = term_category(term);
        let class = lean_class(layer.regime, category).ok_or(LeanCodecError::ClassNotInRegime {
            term: index,
            opcode: u16::from(category.tag()),
        })?;
        let coeff = coefficient_field(index, term.coefficient())?;
        let (source_a, source_b) = source_slots(index, term, layer.sources.len())?;
        words.push((class << LEAN_CLASS_SHIFT) | coeff);
        words.push(source_a);
        words.push(source_b);
        words.push(0);
    }
    Ok(LeanProgram { words, term_count: order.len() })
}

/// The header's coefficient field: the recipe id itself, thirteen bits wide.
fn coefficient_field(term: usize, id: CoefficientRecipeId) -> Result<u16, LeanCodecError> {
    let coeff = u16::try_from(id.0).unwrap_or(u16::MAX);
    if coeff > LEAN_COEFFICIENT_MASK {
        return Err(LeanCodecError::CoefficientOutOfRange { term, coeff });
    }
    Ok(coeff)
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

/// Unpack the whole stream. Regime-free: it checks the stream's LENGTH and its
/// reserved words and reads the fields, which is everything the words alone
/// determine. [`validate_program`] is what decides legality.
pub fn decode_program(program: &LeanProgram) -> Result<Vec<LeanTerm>, LeanCodecError> {
    let expected = program.term_count.saturating_mul(LEAN_WORDS_PER_TERM);
    if program.words.len() != expected {
        return Err(LeanCodecError::TruncatedStream { words: program.words.len() });
    }
    let mut out = Vec::with_capacity(program.term_count);
    for (term, record) in program.words.chunks_exact(LEAN_WORDS_PER_TERM).enumerate() {
        if record[3] != 0 {
            return Err(LeanCodecError::ReservedWordNonZero { term });
        }
        out.push(LeanTerm {
            class: ((record[0] >> LEAN_CLASS_SHIFT) & LEAN_CLASS_MASK) as u8,
            coeff: (record[0] >> LEAN_COEFFICIENT_SHIFT) & LEAN_COEFFICIENT_MASK,
            source_a: record[1],
            source_b: record[2],
        });
    }
    Ok(out)
}

/// Accept only a stream `layer` can execute: every class live in its regime,
/// every coefficient id addressable, every slot inside the source table, and
/// `source_b` present exactly for the two-source classes.
pub fn validate_program(program: &LeanProgram, layer: &CoeffLayer) -> Result<(), LeanCodecError> {
    let terms = decode_program(program)?;
    let coefficients = CoefficientRecipeId::RESERVED as usize + layer.coefficients.len();
    for (term, decoded) in terms.iter().enumerate() {
        let class = u16::from(decoded.class);
        let category = lean_category(layer.regime, class)
            .ok_or(LeanCodecError::ClassNotInRegime { term, opcode: class })?;
        if usize::from(decoded.coeff) >= coefficients {
            return Err(LeanCodecError::CoefficientOutOfRange { term, coeff: decoded.coeff });
        }
        if usize::from(decoded.source_a) >= layer.sources.len() {
            return Err(LeanCodecError::SourceOutOfRange { term, slot: decoded.source_a });
        }
        if category_arity(category) == 1 {
            if decoded.source_b != SOURCE_NONE {
                return Err(LeanCodecError::SourceBMustBeNone { term });
            }
        } else {
            if decoded.source_b == SOURCE_NONE {
                return Err(LeanCodecError::SourceBMissing { term });
            }
            if usize::from(decoded.source_b) >= layer.sources.len() {
                return Err(LeanCodecError::SourceOutOfRange { term, slot: decoded.source_b });
            }
        }
    }
    Ok(())
}

// ── Disassembly ──────────────────────────────────────────────────────────────

/// Render the program as text: a header line, then ONE line per record —
/// `word offset`, mnemonic, coefficient (`+1` / `-1` / `#bank`), then each
/// source as `s{slot}:{width}`.
///
/// Infallible on purpose, since a malformed program is exactly when this is
/// read: a dead class prints as `class{n}?`, a slot past the source table as
/// `s{n}:?`, and a length disagreement shows in the header's `terms` versus
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
    let records = program.words.chunks_exact(LEAN_WORDS_PER_TERM).take(program.term_count);
    for (index, record) in records.enumerate() {
        let class = (record[0] >> LEAN_CLASS_SHIFT) & LEAN_CLASS_MASK;
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
        let _ = writeln!(
            out,
            "{:04}  {mnemonic:<14}  k={:<5}  {}",
            index * LEAN_WORDS_PER_TERM,
            coefficient_tag((record[0] >> LEAN_COEFFICIENT_SHIFT) & LEAN_COEFFICIENT_MASK),
            operands.join("  |  "),
        );
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
    use crate::bwd::coeff::model::{CoeffSource, NormalizedCoefficientRecipe, ProjectionId};
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
            decode_program(&program).expect("the encoder emits whole records"),
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
        let decoded = decode_program(&program).expect("whole records");
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
        assert_eq!(decode_program(&program), Ok(Vec::new()));
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

    /// Class 2 is dead in the continuation regime.
    #[test]
    fn validate_rejects_a_dead_class() {
        let layer = ext_layer();
        let program = LeanProgram { words: record(2, 0, 0, SOURCE_NONE).to_vec(), term_count: 1 };
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::ClassNotInRegime { term: 0, opcode: 2 }),
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
        assert_eq!(decode_program(&program), Err(LeanCodecError::ReservedWordNonZero { term: 1 }));
        assert_eq!(
            validate_program(&program, &layer),
            Err(LeanCodecError::ReservedWordNonZero { term: 1 }),
        );
    }

    /// A fixed-width stream has ONE legal length: a partial record and a
    /// trailing word are the same defect.
    #[test]
    fn decode_rejects_a_stream_that_is_not_whole_records() {
        let layer = ext_layer();
        let words = record(0, 0, 1, SOURCE_NONE).to_vec();
        for length in [3usize, 5] {
            let mut short = words.clone();
            short.resize(length, 0);
            let program = LeanProgram { words: short, term_count: 1 };
            assert_eq!(
                decode_program(&program),
                Err(LeanCodecError::TruncatedStream { words: length }),
            );
            assert_eq!(
                validate_program(&program, &layer),
                Err(LeanCodecError::TruncatedStream { words: length }),
            );
        }
        let two_records = LeanProgram { words: words.clone(), term_count: 2 };
        assert_eq!(
            decode_program(&two_records),
            Err(LeanCodecError::TruncatedStream { words: 4 }),
            "term_count disagreeing with the stream is the same defect",
        );
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

    /// A dead class and a slot past the source table still render, because a
    /// malformed program is exactly what gets disassembled.
    #[test]
    fn disassembles_a_malformed_program() {
        let layer = ext_layer();
        let mut words = record(2, 0, 0, 1).to_vec();
        words.extend(record(1, 0, 9, 1));
        let program = LeanProgram { words, term_count: 2 };
        assert_eq!(
            disassemble(&program, &layer),
            "\
; lean program regime=Ext terms=2 words=8 bytes=16
0000  class2?         k=+1     s0:e4  |  s1:e4
0004  DualProductE4   k=+1     s9:?  |  s1:e4
",
        );
    }

    #[test]
    fn program_survives_a_serde_roundtrip() {
        let layer = ext_layer();
        let program = encode_program(&layer, &order_terms(&layer)).expect("a legal Ext layer");
        let json = serde_json::to_string(&program).expect("plain data");
        assert_eq!(serde_json::from_str::<LeanProgram>(&json).expect("plain data"), program);
    }
}
