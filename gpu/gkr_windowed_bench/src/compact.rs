use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::artifact::{
    decode_program, validate_artifact, FrozenArtifact, FrozenField, WindowAtom, WindowClass,
    WindowTerm, GROUP_PRODUCT_PREFIX_COUNT_MASK, IMMEDIATE_ID_MASK, REDUCE_AFTER, SOURCE_NONE,
};
use crate::lazy_segments::{plan_lazy_segments, MAX_INNER_PRODUCTS};

pub const COMPACT_WORD_CAPACITY: usize = 350;

const TAG_SHIFT: u32 = 28;
const TAG_MASK: u32 = 0xf;
const TAG_COMPACT_ATOM: u32 = 0xf;
const TAG_BLOCK: u32 = 0xe;
const TAG_LINEAR_SINGLETON: u32 = 0xd;
const TAG_PRODUCT_SINGLETON: u32 = 0xc;

const ATOM_FIELD_SHIFT: u32 = 27;
const ATOM_CORE_SHIFT: u32 = 20;
const ATOM_ARITY_SHIFT: u32 = 12;
const ATOM_PREFIX_SHIFT: u32 = 4;
const ATOM_RESERVED_MASK: u32 = 0xf;
const ATOM_SPAN_MASK: u32 = 0x1ff;
const ATOM_TAIL_SHIFT: u32 = 9;
const ATOM_CANONICAL_SHIFT: u32 = 18;
const ATOM_WORD1_RESERVED_MASK: u32 = 0xfc00_0000;

const BLOCK_FAMILY_SHIFT: u32 = 25;
const BLOCK_ROLE_SHIFT: u32 = 24;
const BLOCK_REPRESENTATION_SHIFT: u32 = 23;
const BLOCK_IMMEDIATE_SHIFT: u32 = 16;
const BLOCK_MEMBER_SHIFT: u32 = 8;
const BLOCK_WINDOW_B_SHIFT: u32 = 6;
const BLOCK_CANONICAL_SHIFT: u32 = 12;
const BLOCK_WORD1_RESERVED_MASK: u32 = 0xfff0_0000;

const SINGLETON_COEFFICIENT_SHIFT: u32 = 21;
const SINGLETON_SOURCE_SHIFT: u32 = 8;
const SINGLETON_RESERVED_MASK: u32 = 0xff;
const PRODUCT_WORD1_RESERVED_MASK: u32 = 0xffff_e000;
const COORDINATE_MASK: u32 = 0x1fff;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompactFamily {
    SameWindowProduct,
    DirectProduct,
    SameWindowLinear,
    DirectLinear,
    Escape,
}

impl CompactFamily {
    fn code(self) -> u32 {
        match self {
            Self::SameWindowProduct => 0,
            Self::DirectProduct => 1,
            Self::SameWindowLinear => 2,
            Self::DirectLinear => 3,
            Self::Escape => 4,
        }
    }

    fn decode(code: u32) -> Result<Self, CompactError> {
        match code {
            0 => Ok(Self::SameWindowProduct),
            1 => Ok(Self::DirectProduct),
            2 => Ok(Self::SameWindowLinear),
            3 => Ok(Self::DirectLinear),
            4 => Ok(Self::Escape),
            _ => Err(CompactError::InvalidTag { word: 0, tag: code }),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtomEncoding {
    LegacyPassthrough,
    Compact,
    LinearSingleton,
    ProductSingleton,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanonicalSlot {
    pub canonical_record: u16,
    pub word: u16,
    pub lane: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactProgramV1 {
    pub words: Vec<u32>,
    pub bf_word_count: u16,
    pub canonical_record_count: u16,
    pub slots: Vec<CanonicalSlot>,
    pub coefficient_count: u16,
    pub immediate_count: u16,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactPolicy {
    pub direct_product_prefix: bool,
    pub same_window_product_prefix: bool,
    pub compact_linear_singleton: bool,
    pub permute_within_segment: bool,
}

impl CompactPolicy {
    pub const PASSTHROUGH: Self = Self {
        direct_product_prefix: false,
        same_window_product_prefix: false,
        compact_linear_singleton: false,
        permute_within_segment: false,
    };

    pub const DIRECT_PREFIX: Self = Self {
        direct_product_prefix: true,
        ..Self::PASSTHROUGH
    };
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedCompactAtom {
    pub encoding: AtomEncoding,
    pub field: FrozenField,
    pub core: u16,
    pub product_prefix: u16,
    pub members: Vec<WindowTerm>,
    pub canonical_records: Vec<u16>,
    pub word_span: u16,
    pub tail_word_span: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompactError {
    Artifact(String),
    InputAtomsMismatch,
    ReservedRegionOverflow {
        required: usize,
        maximum: usize,
    },
    FieldWidth {
        field: &'static str,
        required_bits: u8,
        available_bits: u8,
    },
    NonzeroReservedBits {
        word: usize,
    },
    TruncatedHeader {
        word: usize,
    },
    TruncatedPayload {
        word: usize,
    },
    WrongTotalSpan {
        word: usize,
        declared: usize,
        observed: usize,
    },
    WrongTailSpan {
        word: usize,
        declared: usize,
        observed: usize,
    },
    PassthroughArityMismatch {
        record: u16,
    },
    BfE4Crossing {
        record: u16,
    },
    AtomCrossing {
        word: usize,
    },
    FiveProductSegment {
        record: u16,
    },
    MemberPayloadMismatch {
        word: usize,
    },
    EscapePayloadUnderCompactTag {
        word: usize,
    },
    InvalidTag {
        word: usize,
        tag: u32,
    },
    InvalidCoefficient {
        word: usize,
        coefficient: u16,
    },
    InvalidImmediate {
        word: usize,
        immediate: u16,
    },
    MissingCanonicalRecord {
        record: u16,
    },
    DuplicateCanonicalRecord {
        record: u16,
    },
    CanonicalSlotMismatch {
        record: u16,
    },
    MalformedAtom {
        word: usize,
    },
}

impl core::fmt::Display for CompactError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for CompactError {}

fn required_bits(value: usize) -> u8 {
    if value == 0 {
        0
    } else {
        (usize::BITS - value.leading_zeros()) as u8
    }
}

fn fit(value: usize, bits: u8, field: &'static str) -> Result<u32, CompactError> {
    if required_bits(value) > bits {
        return Err(CompactError::FieldWidth {
            field,
            required_bits: required_bits(value),
            available_bits: bits,
        });
    }
    Ok(value as u32)
}

fn raw_words(term_class: u16, factor: u16, source_a: u16, source_b: u16) -> [u32; 2] {
    [
        u32::from(term_class) | (u32::from(factor) << 16),
        u32::from(source_a) | (u32::from(source_b) << 16),
    ]
}

fn raw_instruction(instruction: crate::abi::WindowInstruction) -> [u32; 2] {
    raw_words(
        instruction.term_class,
        instruction.factor,
        instruction.source_a,
        instruction.source_b,
    )
}

fn atom_field(atom: &WindowAtom) -> FrozenField {
    match atom {
        WindowAtom::GroupBf { .. } => FrozenField::Base,
        WindowAtom::GroupE4 { .. } => FrozenField::Ext,
        WindowAtom::Term(term) => match term.class {
            WindowClass::LinearBf
            | WindowClass::ProductBfBf
            | WindowClass::LinearBfProceduralA
            | WindowClass::ProductBfBfProceduralB => FrozenField::Base,
            WindowClass::LinearE4 | WindowClass::ProductBfE4 | WindowClass::ProductE4E4 => {
                FrozenField::Ext
            }
            WindowClass::GroupBf | WindowClass::GroupE4 => unreachable!(),
        },
    }
}

fn atom_record_count(atom: &WindowAtom) -> usize {
    match atom {
        WindowAtom::Term(_) => 1,
        WindowAtom::GroupBf { members, .. } | WindowAtom::GroupE4 { members, .. } => {
            members.len() + 1
        }
    }
}

fn push_slot(
    slots: &mut Vec<CanonicalSlot>,
    canonical_record: usize,
    word: usize,
    lane: u8,
) -> Result<(), CompactError> {
    slots.push(CanonicalSlot {
        canonical_record: fit(canonical_record, 16, "canonical_slot_record")? as u16,
        word: fit(word, 16, "canonical_slot_word")? as u16,
        lane,
    });
    Ok(())
}

fn encode_passthrough(
    artifact: &FrozenArtifact,
    canonical_head: usize,
    records: usize,
    words: &mut Vec<u32>,
    slots: &mut Vec<CanonicalSlot>,
) -> Result<(), CompactError> {
    for record in canonical_head..canonical_head + records {
        push_slot(slots, record, words.len(), 0)?;
        words.extend(raw_instruction(artifact.program[record]));
    }
    Ok(())
}

fn same_window_pair(term: &WindowTerm) -> Option<(u16, u16)> {
    if term.source_a == SOURCE_NONE || term.source_b == SOURCE_NONE {
        return None;
    }
    let window_a = term.source_a >> 7;
    let window_b = term.source_b >> 7;
    (window_a < 64 && window_b < 64).then_some((window_a, window_b))
}

fn block_header(
    family: CompactFamily,
    immediate: u16,
    members: usize,
    payload_words: usize,
    window_a: u16,
    window_b: u16,
    canonical_first: usize,
) -> Result<[u32; 2], CompactError> {
    let role = u32::from(matches!(
        family,
        CompactFamily::SameWindowLinear | CompactFamily::DirectLinear | CompactFamily::Escape
    ));
    let representation = u32::from(matches!(
        family,
        CompactFamily::SameWindowProduct | CompactFamily::SameWindowLinear
    ));
    let word0 = TAG_BLOCK << TAG_SHIFT
        | family.code() << BLOCK_FAMILY_SHIFT
        | role << BLOCK_ROLE_SHIFT
        | representation << BLOCK_REPRESENTATION_SHIFT
        | fit(usize::from(immediate), 7, "immediate")? << BLOCK_IMMEDIATE_SHIFT
        | fit(members, 8, "member_count")? << BLOCK_MEMBER_SHIFT
        | fit(payload_words, 8, "payload_words")?;
    let word1 = fit(usize::from(window_a), 6, "window_a")?
        | fit(usize::from(window_b), 6, "window_b")? << BLOCK_WINDOW_B_SHIFT
        | fit(canonical_first, 8, "canonical_first_record")? << BLOCK_CANONICAL_SHIFT;
    Ok([word0, word1])
}

fn encode_compact_group(
    core: u16,
    lazy_product_count: u16,
    members: &[WindowTerm],
    artifact: &FrozenArtifact,
    canonical_head: usize,
    policy: CompactPolicy,
    words: &mut Vec<u32>,
    slots: &mut Vec<CanonicalSlot>,
) -> Result<(), CompactError> {
    let prefix = usize::from(lazy_product_count);
    if prefix < 2
        || prefix > members.len()
        || !members[..prefix]
            .iter()
            .all(|member| member.class == WindowClass::ProductBfBf)
        || !members[prefix..]
            .iter()
            .all(|member| member.class == WindowClass::LinearBf)
    {
        return Err(CompactError::MalformedAtom { word: words.len() });
    }
    fit(usize::from(core), 7, "core_coefficient")?;
    fit(members.len(), 8, "arity")?;
    fit(prefix, 8, "product_prefix")?;
    fit(canonical_head, 8, "canonical_head_record")?;

    let mut products = members[..prefix]
        .iter()
        .copied()
        .enumerate()
        .map(|(index, member)| (member, canonical_head + 1 + index))
        .collect::<Vec<_>>();
    if policy.permute_within_segment {
        let plan = plan_lazy_segments(prefix)
            .map_err(|error| CompactError::Artifact(error.to_string()))?;
        let mut start = 0usize;
        for end in plan.segment_ends {
            products[start..usize::from(end)]
                .sort_by_key(|(member, _)| (member.coefficient, member.source_a, member.source_b));
            start = usize::from(end);
        }
    }

    let atom_start = words.len();
    words.extend([0, 0]);
    push_slot(slots, canonical_head, atom_start, 0)?;

    let mut index = 0usize;
    while index < products.len() {
        let immediate = products[index].0.coefficient;
        let mut end = index + 1;
        while end < products.len() && products[end].0.coefficient == immediate {
            end += 1;
        }
        let run = &products[index..end];
        let first_pair = same_window_pair(&run[0].0);
        let use_same_window = policy.same_window_product_prefix
            && first_pair.is_some()
            && run
                .iter()
                .all(|(member, _)| same_window_pair(member) == first_pair);
        let window_pair = use_same_window.then_some(first_pair.unwrap());
        let payload_words = if use_same_window {
            run.len().div_ceil(2)
        } else {
            run.len()
        };
        let (window_a, window_b) = window_pair.unwrap_or((0, 0));
        words.extend(block_header(
            if use_same_window {
                CompactFamily::SameWindowProduct
            } else {
                CompactFamily::DirectProduct
            },
            immediate,
            run.len(),
            payload_words,
            window_a,
            window_b,
            run[0].1,
        )?);
        if use_same_window {
            for pair in run.chunks(2) {
                let payload_word = words.len();
                let mut payload = 0u32;
                for (lane, (member, canonical_record)) in pair.iter().enumerate() {
                    let (observed_a, observed_b) = same_window_pair(member).unwrap();
                    if (observed_a, observed_b) != (window_a, window_b) {
                        return Err(CompactError::MalformedAtom { word: payload_word });
                    }
                    let packed = u32::from(member.source_a & 0x7f)
                        | (u32::from(member.source_b & 0x7f) << 7);
                    payload |= packed << (14 * lane);
                    push_slot(slots, *canonical_record, payload_word, lane as u8)?;
                }
                words.push(payload);
            }
        } else {
            for (member, canonical_record) in run {
                fit(usize::from(member.source_a), 13, "source_coordinate")?;
                fit(usize::from(member.source_b), 13, "source_coordinate")?;
                let payload_word = words.len();
                words.push(u32::from(member.source_a) | (u32::from(member.source_b) << 13));
                push_slot(slots, *canonical_record, payload_word, 0)?;
            }
        }
        index = end;
    }

    let tail_start = words.len();
    let tail = &members[prefix..];
    if !tail.is_empty() {
        words.extend(block_header(
            CompactFamily::Escape,
            0,
            tail.len(),
            2 * tail.len(),
            0,
            0,
            canonical_head + 1 + prefix,
        )?);
        for record in canonical_head + 1 + prefix..canonical_head + 1 + members.len() {
            push_slot(slots, record, words.len(), 0)?;
            words.extend(raw_instruction(artifact.program[record]));
        }
    }
    let total_span = words.len() - atom_start;
    let tail_span = words.len() - tail_start;
    let field = 0u32;
    words[atom_start] = TAG_COMPACT_ATOM << TAG_SHIFT
        | field << ATOM_FIELD_SHIFT
        | fit(usize::from(core), 7, "core_coefficient")? << ATOM_CORE_SHIFT
        | fit(members.len(), 8, "arity")? << ATOM_ARITY_SHIFT
        | fit(prefix, 8, "product_prefix")? << ATOM_PREFIX_SHIFT;
    words[atom_start + 1] = fit(total_span, 9, "total_word_span")?
        | fit(tail_span, 9, "tail_word_span")? << ATOM_TAIL_SHIFT
        | fit(canonical_head, 8, "canonical_head_record")? << ATOM_CANONICAL_SHIFT;
    Ok(())
}

pub fn encode_compact_program(
    atoms: &[WindowAtom],
    artifact: &FrozenArtifact,
    policy: CompactPolicy,
) -> Result<CompactProgramV1, CompactError> {
    if policy == CompactPolicy::PASSTHROUGH
        && artifact.program.len().saturating_mul(2) > COMPACT_WORD_CAPACITY
    {
        return Err(CompactError::ReservedRegionOverflow {
            required: artifact.program.len().saturating_mul(2),
            maximum: COMPACT_WORD_CAPACITY,
        });
    }
    validate_artifact(artifact).map_err(|error| CompactError::Artifact(error.to_string()))?;
    let decoded = decode_program(artifact)
        .map_err(|error| CompactError::Artifact(error.to_string()))?
        .0;
    if decoded != atoms {
        return Err(CompactError::InputAtomsMismatch);
    }
    let coefficient_count =
        fit(artifact.coefficient_count as usize, 16, "coefficient_count")? as u16;
    let immediate_count = fit(artifact.immediates.len(), 16, "immediate_count")? as u16;
    let canonical_record_count = fit(artifact.program.len(), 16, "canonical_record_count")? as u16;
    let mut words = Vec::with_capacity(COMPACT_WORD_CAPACITY);
    let mut slots = Vec::with_capacity(artifact.program.len());
    let mut canonical_head = 0usize;
    let mut bf_word_count = None;
    let mut seen_ext = false;
    for atom in atoms {
        let field = atom_field(atom);
        if field == FrozenField::Ext {
            if !seen_ext {
                bf_word_count = Some(words.len());
                seen_ext = true;
            }
        } else if seen_ext {
            return Err(CompactError::BfE4Crossing {
                record: canonical_head as u16,
            });
        }
        let records = atom_record_count(atom);
        match atom {
            WindowAtom::GroupBf {
                core,
                lazy_product_count,
                members,
            } if *lazy_product_count >= 2
                && (policy.direct_product_prefix || policy.same_window_product_prefix) =>
            {
                encode_compact_group(
                    *core,
                    *lazy_product_count,
                    members,
                    artifact,
                    canonical_head,
                    policy,
                    &mut words,
                    &mut slots,
                )?;
            }
            WindowAtom::Term(term)
                if policy.compact_linear_singleton
                    && term.class == WindowClass::LinearBf
                    && term.source_a != SOURCE_NONE =>
            {
                fit(usize::from(term.coefficient), 7, "singleton_coefficient")?;
                fit(usize::from(term.source_a), 13, "source_coordinate")?;
                let word = words.len();
                words.push(
                    TAG_LINEAR_SINGLETON << TAG_SHIFT
                        | u32::from(term.coefficient) << SINGLETON_COEFFICIENT_SHIFT
                        | u32::from(term.source_a) << SINGLETON_SOURCE_SHIFT,
                );
                push_slot(&mut slots, canonical_head, word, 0)?;
            }
            _ => encode_passthrough(artifact, canonical_head, records, &mut words, &mut slots)?,
        }
        canonical_head += records;
    }
    if canonical_head != artifact.program.len() {
        return Err(CompactError::PassthroughArityMismatch {
            record: canonical_head as u16,
        });
    }
    if words.len() > COMPACT_WORD_CAPACITY {
        return Err(CompactError::ReservedRegionOverflow {
            required: words.len(),
            maximum: COMPACT_WORD_CAPACITY,
        });
    }
    let program = CompactProgramV1 {
        bf_word_count: fit(bf_word_count.unwrap_or(words.len()), 16, "bf_word_count")? as u16,
        words,
        canonical_record_count,
        slots,
        coefficient_count,
        immediate_count,
    };
    decode_compact_program(&program)?;
    Ok(program)
}

fn legacy_term(words: &[u32], word: usize) -> Result<(u16, u16, u16, u16), CompactError> {
    if word + 1 >= words.len() {
        return Err(CompactError::TruncatedPayload { word });
    }
    Ok((
        words[word] as u16,
        (words[word] >> 16) as u16,
        words[word + 1] as u16,
        (words[word + 1] >> 16) as u16,
    ))
}

fn decoded_term(
    class: u16,
    factor: u16,
    source_a: u16,
    source_b: u16,
    group_member: bool,
) -> Result<WindowTerm, CompactError> {
    let class_u8 = u8::try_from(class).map_err(|_| CompactError::InvalidTag {
        word: 0,
        tag: u32::from(class),
    })?;
    let class = WindowClass::try_from(class_u8).map_err(|_| CompactError::InvalidTag {
        word: 0,
        tag: u32::from(class_u8),
    })?;
    Ok(WindowTerm {
        class,
        coefficient: if group_member {
            factor & IMMEDIATE_ID_MASK
        } else {
            factor
        },
        source_a,
        source_b,
    })
}

fn validate_coefficient(
    program: &CompactProgramV1,
    word: usize,
    coefficient: u16,
) -> Result<(), CompactError> {
    if coefficient >= program.coefficient_count {
        return Err(CompactError::InvalidCoefficient { word, coefficient });
    }
    Ok(())
}

fn validate_immediate(
    program: &CompactProgramV1,
    word: usize,
    immediate: u16,
) -> Result<(), CompactError> {
    if usize::from(immediate) >= usize::from(program.immediate_count) + 2 {
        return Err(CompactError::InvalidImmediate { word, immediate });
    }
    Ok(())
}

fn validate_legacy_segments(
    program: &CompactProgramV1,
    head_word: usize,
    canonical_head: u16,
    arity: usize,
    prefix: usize,
) -> Result<(), CompactError> {
    let mut products = 0usize;
    for member in 0..prefix {
        let word = head_word + 2 * (member + 1);
        let (class, factor, _, _) = legacy_term(&program.words, word)?;
        if class != WindowClass::ProductBfBf as u16 {
            return Err(CompactError::PassthroughArityMismatch {
                record: canonical_head,
            });
        }
        validate_immediate(program, word, factor & IMMEDIATE_ID_MASK)?;
        products += 1;
        if products > usize::from(MAX_INNER_PRODUCTS) {
            return Err(CompactError::FiveProductSegment {
                record: canonical_head + 1 + member as u16,
            });
        }
        if factor & REDUCE_AFTER != 0 {
            products = 0;
        }
    }
    if prefix > arity {
        return Err(CompactError::PassthroughArityMismatch {
            record: canonical_head,
        });
    }
    Ok(())
}

fn decode_passthrough(
    program: &CompactProgramV1,
    word: usize,
    canonical_head: u16,
    expected_slots: &mut Vec<CanonicalSlot>,
) -> Result<DecodedCompactAtom, CompactError> {
    let (class, factor, source_a, source_b) = legacy_term(&program.words, word)?;
    let class_u8 = u8::try_from(class).map_err(|_| CompactError::InvalidTag {
        word,
        tag: u32::from(class),
    })?;
    let class_kind = WindowClass::try_from(class_u8).map_err(|_| CompactError::InvalidTag {
        word,
        tag: u32::from(class),
    })?;
    let (field, core, prefix, records) = match class_kind {
        WindowClass::GroupBf => (
            FrozenField::Base,
            factor,
            source_b & GROUP_PRODUCT_PREFIX_COUNT_MASK,
            usize::from(source_a) + 1,
        ),
        WindowClass::GroupE4 => (FrozenField::Ext, factor, 0, 3),
        WindowClass::LinearBf
        | WindowClass::ProductBfBf
        | WindowClass::LinearBfProceduralA
        | WindowClass::ProductBfBfProceduralB => (FrozenField::Base, factor, 0, 1),
        WindowClass::LinearE4 | WindowClass::ProductBfE4 | WindowClass::ProductE4E4 => {
            (FrozenField::Ext, factor, 0, 1)
        }
    };
    if word + 2 * records > program.words.len() {
        return Err(CompactError::PassthroughArityMismatch {
            record: canonical_head,
        });
    }
    if matches!(class_kind, WindowClass::GroupBf | WindowClass::GroupE4) {
        validate_coefficient(program, word, factor)?;
    } else {
        validate_coefficient(program, word, factor)?;
    }
    if class_kind == WindowClass::GroupBf && prefix >= 2 {
        validate_legacy_segments(
            program,
            word,
            canonical_head,
            records - 1,
            usize::from(prefix),
        )?;
    }
    let mut members = Vec::with_capacity(records.saturating_sub(1).max(1));
    if records == 1 {
        members.push(decoded_term(class, factor, source_a, source_b, false)?);
    } else {
        for member in 0..records - 1 {
            let member_word = word + 2 * (member + 1);
            let (member_class, member_factor, member_a, member_b) =
                legacy_term(&program.words, member_word)?;
            members.push(decoded_term(
                member_class,
                member_factor,
                member_a,
                member_b,
                true,
            )?);
        }
    }
    let canonical_records = (canonical_head..canonical_head + records as u16).collect::<Vec<_>>();
    for (offset, record) in canonical_records.iter().enumerate() {
        expected_slots.push(CanonicalSlot {
            canonical_record: *record,
            word: (word + 2 * offset) as u16,
            lane: 0,
        });
    }
    Ok(DecodedCompactAtom {
        encoding: AtomEncoding::LegacyPassthrough,
        field,
        core,
        product_prefix: prefix,
        members,
        canonical_records,
        word_span: (2 * records) as u16,
        tail_word_span: if prefix == 0 {
            (2 * records.saturating_sub(1)) as u16
        } else {
            (2 * (records - 1 - usize::from(prefix))) as u16
        },
    })
}

fn canonical_record_at(
    program: &CompactProgramV1,
    word: usize,
    lane: u8,
    fallback_record: u16,
) -> Result<u16, CompactError> {
    let mut matches = program
        .slots
        .iter()
        .filter(|slot| usize::from(slot.word) == word && slot.lane == lane);
    let record = matches
        .next()
        .ok_or(CompactError::MissingCanonicalRecord {
            record: fallback_record,
        })?
        .canonical_record;
    if matches.next().is_some() {
        return Err(CompactError::CanonicalSlotMismatch { record });
    }
    Ok(record)
}

fn decode_compact_atom(
    program: &CompactProgramV1,
    word: usize,
    expected_slots: &mut Vec<CanonicalSlot>,
) -> Result<DecodedCompactAtom, CompactError> {
    if word + 1 >= program.words.len() {
        return Err(CompactError::TruncatedHeader { word });
    }
    let atom0 = program.words[word];
    let atom1 = program.words[word + 1];
    if atom0 & ATOM_RESERVED_MASK != 0 || atom1 & ATOM_WORD1_RESERVED_MASK != 0 {
        return Err(CompactError::NonzeroReservedBits { word });
    }
    let field = if atom0 >> ATOM_FIELD_SHIFT & 1 == 0 {
        FrozenField::Base
    } else {
        FrozenField::Ext
    };
    let core = ((atom0 >> ATOM_CORE_SHIFT) & 0x7f) as u16;
    validate_coefficient(program, word, core)?;
    let arity = ((atom0 >> ATOM_ARITY_SHIFT) & 0xff) as usize;
    let prefix = ((atom0 >> ATOM_PREFIX_SHIFT) & 0xff) as usize;
    let total_span = (atom1 & ATOM_SPAN_MASK) as usize;
    let tail_span = ((atom1 >> ATOM_TAIL_SHIFT) & ATOM_SPAN_MASK) as usize;
    let canonical_head = ((atom1 >> ATOM_CANONICAL_SHIFT) & 0xff) as u16;
    if total_span < 2 {
        return Err(CompactError::WrongTotalSpan {
            word,
            declared: total_span,
            observed: 2,
        });
    }
    let atom_end = word
        .checked_add(total_span)
        .ok_or(CompactError::AtomCrossing { word })?;
    if atom_end > program.words.len() {
        return Err(CompactError::AtomCrossing { word });
    }
    if prefix > arity || field != FrozenField::Base {
        return Err(CompactError::MalformedAtom { word });
    }
    let mut cursor = word + 2;
    let mut product_members = 0usize;
    let mut members = Vec::with_capacity(arity);
    let mut canonical_records = vec![canonical_head];
    expected_slots.push(CanonicalSlot {
        canonical_record: canonical_head,
        word: word as u16,
        lane: 0,
    });
    let mut observed_tail_span = 0usize;
    while cursor < atom_end {
        if cursor + 1 >= atom_end {
            return Err(CompactError::TruncatedHeader { word: cursor });
        }
        let block0 = program.words[cursor];
        let block1 = program.words[cursor + 1];
        if block0 >> TAG_SHIFT != TAG_BLOCK {
            return Err(if cursor == word + 2 {
                CompactError::EscapePayloadUnderCompactTag { word: cursor }
            } else {
                CompactError::WrongTotalSpan {
                    word,
                    declared: total_span,
                    observed: cursor - word,
                }
            });
        }
        if block1 & BLOCK_WORD1_RESERVED_MASK != 0 {
            return Err(CompactError::NonzeroReservedBits { word: cursor + 1 });
        }
        let family = CompactFamily::decode((block0 >> BLOCK_FAMILY_SHIFT) & 0x7)?;
        let role = (block0 >> BLOCK_ROLE_SHIFT) & 1;
        let representation = (block0 >> BLOCK_REPRESENTATION_SHIFT) & 1;
        let immediate = ((block0 >> BLOCK_IMMEDIATE_SHIFT) & 0x7f) as u16;
        let member_count = ((block0 >> BLOCK_MEMBER_SHIFT) & 0xff) as usize;
        let payload_words = (block0 & 0xff) as usize;
        let window_a = (block1 & 0x3f) as u16;
        let window_b = ((block1 >> BLOCK_WINDOW_B_SHIFT) & 0x3f) as u16;
        let canonical_first = ((block1 >> BLOCK_CANONICAL_SHIFT) & 0xff) as u16;
        let payload_start = cursor + 2;
        let payload_end = payload_start + payload_words;
        if payload_end > atom_end {
            return Err(CompactError::TruncatedPayload {
                word: payload_start,
            });
        }
        match family {
            CompactFamily::DirectProduct => {
                if role != 0 || representation != 0 || member_count != payload_words {
                    return Err(CompactError::MemberPayloadMismatch { word: cursor });
                }
                validate_immediate(program, cursor, immediate)?;
                for member in 0..member_count {
                    let payload_word = payload_start + member;
                    let payload = program.words[payload_word];
                    if payload >> 26 != 0 {
                        return Err(CompactError::NonzeroReservedBits { word: payload_word });
                    }
                    let source_a = (payload & COORDINATE_MASK) as u16;
                    let source_b = ((payload >> 13) & COORDINATE_MASK) as u16;
                    let fallback_record = canonical_head + 1 + members.len() as u16;
                    let canonical_record =
                        canonical_record_at(program, payload_word, 0, fallback_record)?;
                    if member == 0 && canonical_first != canonical_record {
                        return Err(CompactError::MissingCanonicalRecord {
                            record: canonical_record,
                        });
                    }
                    members.push(WindowTerm {
                        class: WindowClass::ProductBfBf,
                        coefficient: immediate,
                        source_a,
                        source_b,
                    });
                    canonical_records.push(canonical_record);
                    expected_slots.push(CanonicalSlot {
                        canonical_record,
                        word: payload_word as u16,
                        lane: 0,
                    });
                }
                product_members += member_count;
            }
            CompactFamily::SameWindowProduct => {
                if role != 0 || representation != 1 || payload_words != member_count.div_ceil(2) {
                    return Err(CompactError::MemberPayloadMismatch { word: cursor });
                }
                validate_immediate(program, cursor, immediate)?;
                for member in 0..member_count {
                    let payload_word = payload_start + member / 2;
                    let payload = program.words[payload_word];
                    if payload >> 28 != 0 {
                        return Err(CompactError::NonzeroReservedBits { word: payload_word });
                    }
                    let packed = (payload >> (14 * (member % 2))) & 0x3fff;
                    let fallback_record = canonical_head + 1 + members.len() as u16;
                    let lane = (member % 2) as u8;
                    let canonical_record =
                        canonical_record_at(program, payload_word, lane, fallback_record)?;
                    if member == 0 && canonical_first != canonical_record {
                        return Err(CompactError::MissingCanonicalRecord {
                            record: canonical_record,
                        });
                    }
                    members.push(WindowTerm {
                        class: WindowClass::ProductBfBf,
                        coefficient: immediate,
                        source_a: (window_a << 7) | (packed & 0x7f) as u16,
                        source_b: (window_b << 7) | ((packed >> 7) & 0x7f) as u16,
                    });
                    canonical_records.push(canonical_record);
                    expected_slots.push(CanonicalSlot {
                        canonical_record,
                        word: payload_word as u16,
                        lane,
                    });
                }
                product_members += member_count;
            }
            CompactFamily::Escape => {
                if role != 1 || representation != 0 || payload_words != 2 * member_count {
                    return Err(CompactError::MemberPayloadMismatch { word: cursor });
                }
                let expected_first = canonical_head + 1 + members.len() as u16;
                if canonical_first != expected_first {
                    return Err(CompactError::MissingCanonicalRecord {
                        record: expected_first,
                    });
                }
                observed_tail_span = atom_end - cursor;
                for member in 0..member_count {
                    let payload_word = payload_start + 2 * member;
                    let (class, factor, source_a, source_b) =
                        legacy_term(&program.words, payload_word)?;
                    let decoded = decoded_term(class, factor, source_a, source_b, true)?;
                    if decoded.class != WindowClass::LinearBf {
                        return Err(CompactError::MalformedAtom { word: payload_word });
                    }
                    let canonical_record = canonical_first + member as u16;
                    members.push(decoded);
                    canonical_records.push(canonical_record);
                    expected_slots.push(CanonicalSlot {
                        canonical_record,
                        word: payload_word as u16,
                        lane: 0,
                    });
                }
            }
            CompactFamily::SameWindowLinear | CompactFamily::DirectLinear => {
                return Err(CompactError::MalformedAtom { word: cursor });
            }
        }
        cursor = payload_end;
    }
    if cursor != atom_end {
        return Err(CompactError::WrongTotalSpan {
            word,
            declared: total_span,
            observed: cursor - word,
        });
    }
    if product_members != prefix || members.len() != arity {
        return Err(CompactError::MemberPayloadMismatch { word });
    }
    let observed_records = canonical_records.iter().copied().collect::<BTreeSet<_>>();
    let expected_records =
        (canonical_head..=canonical_head + arity as u16).collect::<BTreeSet<_>>();
    if observed_records != expected_records {
        let missing = expected_records
            .difference(&observed_records)
            .next()
            .copied()
            .unwrap_or(canonical_head);
        return Err(CompactError::MissingCanonicalRecord { record: missing });
    }
    if observed_tail_span != tail_span {
        return Err(CompactError::WrongTailSpan {
            word,
            declared: tail_span,
            observed: observed_tail_span,
        });
    }
    Ok(DecodedCompactAtom {
        encoding: AtomEncoding::Compact,
        field,
        core,
        product_prefix: prefix as u16,
        members,
        canonical_records,
        word_span: total_span as u16,
        tail_word_span: tail_span as u16,
    })
}

fn decode_linear_singleton(
    program: &CompactProgramV1,
    word: usize,
    canonical_record: u16,
    expected_slots: &mut Vec<CanonicalSlot>,
) -> Result<DecodedCompactAtom, CompactError> {
    let encoded = program.words[word];
    if encoded & SINGLETON_RESERVED_MASK != 0 {
        return Err(CompactError::NonzeroReservedBits { word });
    }
    let coefficient = ((encoded >> SINGLETON_COEFFICIENT_SHIFT) & 0x7f) as u16;
    validate_coefficient(program, word, coefficient)?;
    let source_a = ((encoded >> SINGLETON_SOURCE_SHIFT) & COORDINATE_MASK) as u16;
    expected_slots.push(CanonicalSlot {
        canonical_record,
        word: word as u16,
        lane: 0,
    });
    Ok(DecodedCompactAtom {
        encoding: AtomEncoding::LinearSingleton,
        field: FrozenField::Base,
        core: coefficient,
        product_prefix: 0,
        members: vec![WindowTerm {
            class: WindowClass::LinearBf,
            coefficient,
            source_a,
            source_b: SOURCE_NONE,
        }],
        canonical_records: vec![canonical_record],
        word_span: 1,
        tail_word_span: 0,
    })
}

fn decode_product_singleton(
    program: &CompactProgramV1,
    word: usize,
    canonical_record: u16,
    expected_slots: &mut Vec<CanonicalSlot>,
) -> Result<DecodedCompactAtom, CompactError> {
    if word + 1 >= program.words.len() {
        return Err(CompactError::TruncatedPayload { word });
    }
    let first = program.words[word];
    let second = program.words[word + 1];
    if first & SINGLETON_RESERVED_MASK != 0 || second & PRODUCT_WORD1_RESERVED_MASK != 0 {
        return Err(CompactError::NonzeroReservedBits { word });
    }
    let coefficient = ((first >> SINGLETON_COEFFICIENT_SHIFT) & 0x7f) as u16;
    validate_coefficient(program, word, coefficient)?;
    let source_a = ((first >> SINGLETON_SOURCE_SHIFT) & COORDINATE_MASK) as u16;
    let source_b = (second & COORDINATE_MASK) as u16;
    expected_slots.push(CanonicalSlot {
        canonical_record,
        word: word as u16,
        lane: 0,
    });
    Ok(DecodedCompactAtom {
        encoding: AtomEncoding::ProductSingleton,
        field: FrozenField::Base,
        core: coefficient,
        product_prefix: 1,
        members: vec![WindowTerm {
            class: WindowClass::ProductBfBf,
            coefficient,
            source_a,
            source_b,
        }],
        canonical_records: vec![canonical_record],
        word_span: 2,
        tail_word_span: 0,
    })
}

pub fn decode_compact_program(
    program: &CompactProgramV1,
) -> Result<Vec<DecodedCompactAtom>, CompactError> {
    if program.words.len() > COMPACT_WORD_CAPACITY {
        return Err(CompactError::ReservedRegionOverflow {
            required: program.words.len(),
            maximum: COMPACT_WORD_CAPACITY,
        });
    }
    if program.slots.len() != usize::from(program.canonical_record_count) {
        return Err(CompactError::MissingCanonicalRecord {
            record: program.slots.len() as u16,
        });
    }
    let mut records = BTreeSet::new();
    let mut locations = BTreeSet::new();
    for slot in &program.slots {
        if !records.insert(slot.canonical_record) {
            return Err(CompactError::DuplicateCanonicalRecord {
                record: slot.canonical_record,
            });
        }
        if slot.canonical_record >= program.canonical_record_count
            || usize::from(slot.word) >= program.words.len()
            || !locations.insert((slot.word, slot.lane))
        {
            return Err(CompactError::CanonicalSlotMismatch {
                record: slot.canonical_record,
            });
        }
    }
    if records.len() != usize::from(program.canonical_record_count) {
        let record = (0..program.canonical_record_count)
            .find(|record| !records.contains(record))
            .unwrap_or(program.canonical_record_count);
        return Err(CompactError::MissingCanonicalRecord { record });
    }
    let mut atoms = Vec::new();
    let mut expected_slots = Vec::with_capacity(usize::from(program.canonical_record_count));
    let mut word = 0usize;
    let mut canonical_record = 0u16;
    let mut seen_ext = false;
    while word < program.words.len() {
        let tag = program.words[word] >> TAG_SHIFT & TAG_MASK;
        let atom = match tag {
            TAG_COMPACT_ATOM => decode_compact_atom(program, word, &mut expected_slots)?,
            TAG_LINEAR_SINGLETON => {
                decode_linear_singleton(program, word, canonical_record, &mut expected_slots)?
            }
            TAG_PRODUCT_SINGLETON => {
                decode_product_singleton(program, word, canonical_record, &mut expected_slots)?
            }
            TAG_BLOCK => return Err(CompactError::EscapePayloadUnderCompactTag { word }),
            _ => decode_passthrough(program, word, canonical_record, &mut expected_slots)?,
        };
        let head = *atom
            .canonical_records
            .first()
            .ok_or(CompactError::MissingCanonicalRecord {
                record: canonical_record,
            })?;
        if head != canonical_record {
            return Err(if head < canonical_record {
                CompactError::DuplicateCanonicalRecord { record: head }
            } else {
                CompactError::MissingCanonicalRecord {
                    record: canonical_record,
                }
            });
        }
        if atom.field == FrozenField::Ext {
            if !seen_ext {
                if word != usize::from(program.bf_word_count) {
                    return Err(CompactError::BfE4Crossing {
                        record: canonical_record,
                    });
                }
                seen_ext = true;
            }
        } else if seen_ext {
            return Err(CompactError::BfE4Crossing {
                record: canonical_record,
            });
        }
        canonical_record = canonical_record
            .checked_add(atom.canonical_records.len() as u16)
            .ok_or(CompactError::MissingCanonicalRecord {
                record: canonical_record,
            })?;
        word += usize::from(atom.word_span);
        atoms.push(atom);
    }
    if !seen_ext && usize::from(program.bf_word_count) != program.words.len() {
        return Err(CompactError::BfE4Crossing {
            record: canonical_record,
        });
    }
    if canonical_record != program.canonical_record_count {
        return Err(CompactError::MissingCanonicalRecord {
            record: canonical_record,
        });
    }
    expected_slots.sort_by_key(|slot| slot.canonical_record);
    let mut observed_slots = program.slots.clone();
    observed_slots.sort_by_key(|slot| slot.canonical_record);
    for record in 0..program.canonical_record_count {
        let observed = observed_slots.get(usize::from(record));
        let expected = expected_slots.get(usize::from(record));
        if observed != expected {
            return Err(
                if observed.map(|slot| slot.canonical_record) == Some(record) {
                    CompactError::CanonicalSlotMismatch { record }
                } else {
                    CompactError::MissingCanonicalRecord { record }
                },
            );
        }
    }
    Ok(atoms)
}

#[cfg(test)]
fn infinity_cursor_trace(
    program: &CompactProgramV1,
    x0: u8,
    x1: u8,
) -> Result<(usize, usize, usize), CompactError> {
    let atoms = decode_compact_program(program)?;
    let at_infinity = x0 == 2 || x1 == 2;
    let mut cursor = 0usize;
    let mut executed_products = 0usize;
    let mut skipped_members = 0usize;
    for atom in atoms {
        cursor += usize::from(atom.word_span);
        if at_infinity {
            executed_products += usize::from(atom.product_prefix);
            skipped_members += atom.members.len() - usize::from(atom.product_prefix);
        }
    }
    Ok((cursor, executed_products, skipped_members))
}

#[cfg(test)]
mod tests {
    use crate::artifact::{decode_artifact, decode_program, ADD_SUB_LAYER0_BYTES};
    use crate::census::{default_workload_weights, generate_corpus_census, BackwardRegime};

    use super::*;

    fn retained() -> (
        crate::artifact::FrozenArtifact,
        Vec<crate::artifact::WindowAtom>,
    ) {
        let artifact = decode_artifact(ADD_SUB_LAYER0_BYTES).unwrap();
        let atoms = decode_program(&artifact).unwrap().0;
        (artifact, atoms)
    }

    fn passthrough() -> CompactProgramV1 {
        let (artifact, atoms) = retained();
        encode_compact_program(&atoms, &artifact, CompactPolicy::PASSTHROUGH).unwrap()
    }

    fn direct() -> CompactProgramV1 {
        let (artifact, atoms) = retained();
        encode_compact_program(&atoms, &artifact, CompactPolicy::DIRECT_PREFIX).unwrap()
    }

    fn atom_starts(program: &CompactProgramV1) -> Vec<(usize, DecodedCompactAtom)> {
        let mut cursor = 0usize;
        decode_compact_program(program)
            .unwrap()
            .into_iter()
            .map(|atom| {
                let start = cursor;
                cursor += usize::from(atom.word_span);
                (start, atom)
            })
            .collect()
    }

    fn first_compact(program: &CompactProgramV1) -> usize {
        atom_starts(program)
            .into_iter()
            .find(|(_, atom)| atom.encoding == AtomEncoding::Compact)
            .unwrap()
            .0
    }

    fn encoded_same_window_record_ids(program: &CompactProgramV1) -> BTreeSet<u16> {
        let mut records = BTreeSet::new();
        for (atom_start, atom) in atom_starts(program) {
            if atom.encoding != AtomEncoding::Compact {
                continue;
            }
            let atom_end = atom_start + usize::from(atom.word_span);
            let mut cursor = atom_start + 2;
            while cursor < atom_end {
                let block0 = program.words[cursor];
                let family = CompactFamily::decode((block0 >> BLOCK_FAMILY_SHIFT) & 0x7).unwrap();
                let members = ((block0 >> BLOCK_MEMBER_SHIFT) & 0xff) as usize;
                let payload_words = (block0 & 0xff) as usize;
                if family == CompactFamily::SameWindowProduct {
                    for member in 0..members {
                        records.insert(
                            canonical_record_at(
                                program,
                                cursor + 2 + member / 2,
                                (member % 2) as u8,
                                u16::MAX,
                            )
                            .unwrap(),
                        );
                    }
                }
                cursor += 2 + payload_words;
            }
            assert_eq!(cursor, atom_end);
        }
        records
    }

    #[test]
    fn census_and_codec_agree_on_exact_same_window_records() {
        let census = generate_corpus_census(default_workload_weights()).unwrap();
        let coverage = &census
            .coordinates
            .iter()
            .find(|row| {
                row.id.circuit == "add_sub_lui_auipc_mop"
                    && row.id.layer == 0
                    && row.id.regime == BackwardRegime::Ext
            })
            .unwrap()
            .compiler_binding
            .as_ref()
            .unwrap()
            .handler_coverage;
        let (artifact, atoms) = retained();
        let encoded = encode_compact_program(
            &atoms,
            &artifact,
            CompactPolicy {
                same_window_product_prefix: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
        )
        .unwrap();
        let encoded_records = encoded_same_window_record_ids(&encoded);

        assert_eq!(coverage.same_window_records, 43);
        assert_eq!(
            coverage.same_window_record_ids,
            encoded_records.into_iter().collect::<Vec<_>>()
        );
    }

    #[test]
    fn retained_passthrough_and_direct_prefix_have_exact_sizes_and_bijections() {
        let (artifact, atoms) = retained();
        let passthrough =
            encode_compact_program(&atoms, &artifact, CompactPolicy::PASSTHROUGH).unwrap();
        let direct =
            encode_compact_program(&atoms, &artifact, CompactPolicy::DIRECT_PREFIX).unwrap();
        assert_eq!(COMPACT_WORD_CAPACITY, 350);
        assert_eq!(passthrough.words.len(), 350);
        assert_eq!(direct.words.len(), 326);
        assert_eq!(direct.canonical_record_count, 175);
        assert_eq!(direct.slots.len(), 175);
        assert_eq!(
            direct
                .slots
                .iter()
                .map(|slot| slot.canonical_record)
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            175
        );
        assert_eq!(
            decode_compact_program(&passthrough).unwrap().len(),
            atoms.len()
        );
        assert_eq!(decode_compact_program(&direct).unwrap().len(), atoms.len());
    }

    #[test]
    fn direct_decode_preserves_every_atom_and_member() {
        let (artifact, atoms) = retained();
        let program =
            encode_compact_program(&atoms, &artifact, CompactPolicy::DIRECT_PREFIX).unwrap();
        let decoded = decode_compact_program(&program).unwrap();
        for (index, (expected, observed)) in atoms.iter().zip(decoded).enumerate() {
            match expected {
                WindowAtom::Term(term) => {
                    assert_eq!(observed.members, [*term]);
                    assert_eq!(observed.core, term.coefficient);
                    assert_eq!(observed.product_prefix, 0);
                }
                WindowAtom::GroupBf {
                    core,
                    lazy_product_count,
                    members,
                } => {
                    assert_eq!(observed.core, *core);
                    let physical_prefix = if *lazy_product_count == 0
                        && members
                            .first()
                            .is_some_and(|member| member.class == WindowClass::ProductBfBf)
                    {
                        1
                    } else {
                        *lazy_product_count
                    };
                    assert_eq!(
                        observed.product_prefix, physical_prefix,
                        "product prefix differs at atom {index}: {expected:?}"
                    );
                    assert_eq!(observed.members, *members);
                }
                WindowAtom::GroupE4 { core, members } => {
                    assert_eq!(observed.core, *core);
                    assert_eq!(observed.product_prefix, 0);
                    assert_eq!(observed.members, *members);
                }
            }
        }
    }

    #[test]
    fn same_window_and_permutation_axes_do_not_grow_their_parent() {
        let (artifact, atoms) = retained();
        let direct =
            encode_compact_program(&atoms, &artifact, CompactPolicy::DIRECT_PREFIX).unwrap();
        let same_window = encode_compact_program(
            &atoms,
            &artifact,
            CompactPolicy {
                same_window_product_prefix: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
        )
        .unwrap();
        let permuted = encode_compact_program(
            &atoms,
            &artifact,
            CompactPolicy {
                permute_within_segment: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
        )
        .unwrap();
        let same_window_permuted = encode_compact_program(
            &atoms,
            &artifact,
            CompactPolicy {
                same_window_product_prefix: true,
                permute_within_segment: true,
                ..CompactPolicy::DIRECT_PREFIX
            },
        )
        .unwrap();
        assert_eq!(same_window.words.len(), 312);
        assert_eq!(same_window_permuted.words.len(), 311);
        for (same, direct) in decode_compact_program(&same_window)
            .unwrap()
            .into_iter()
            .zip(decode_compact_program(&direct).unwrap())
        {
            assert_eq!(same.field, direct.field);
            assert_eq!(same.core, direct.core);
            assert_eq!(same.product_prefix, direct.product_prefix);
            assert_eq!(same.members, direct.members);
            assert_eq!(same.canonical_records, direct.canonical_records);
        }
        assert!(permuted.words.len() <= direct.words.len());

        for (combined, direct) in decode_compact_program(&same_window_permuted)
            .unwrap()
            .into_iter()
            .zip(decode_compact_program(&direct).unwrap())
        {
            assert_eq!(combined.field, direct.field);
            assert_eq!(combined.core, direct.core);
            assert_eq!(combined.product_prefix, direct.product_prefix);
            let combined_record_offset =
                usize::from(combined.canonical_records.len() == combined.members.len() + 1);
            let by_record = combined
                .canonical_records
                .iter()
                .skip(combined_record_offset)
                .copied()
                .zip(combined.members)
                .collect::<std::collections::BTreeMap<_, _>>();
            let direct_record_offset =
                usize::from(direct.canonical_records.len() == direct.members.len() + 1);
            for (record, member) in direct
                .canonical_records
                .into_iter()
                .skip(direct_record_offset)
                .zip(direct.members)
            {
                assert_eq!(by_record[&record], member);
            }
        }

        let direct_atoms = decode_compact_program(&direct).unwrap();
        let permuted_atoms = decode_compact_program(&permuted).unwrap();
        let mut product_members = 0usize;
        let mut reorderable_members = 0usize;
        let mut moved = Vec::new();
        for (before, after) in direct_atoms.iter().zip(&permuted_atoms) {
            let prefix = usize::from(before.product_prefix);
            if prefix < 2 {
                continue;
            }
            product_members += prefix;
            let plan = plan_lazy_segments(prefix).unwrap();
            let mut start = 0usize;
            for end in plan.segment_ends {
                let end = usize::from(end);
                if end - start >= 2 {
                    reorderable_members += end - start;
                }
                start = end;
            }
            for (&canonical_before, &canonical_after) in before.canonical_records[1..1 + prefix]
                .iter()
                .zip(&after.canonical_records[1..1 + prefix])
            {
                if canonical_before != canonical_after {
                    moved.push((canonical_before, canonical_after));
                }
            }
        }
        assert_eq!(product_members, 72);
        assert_eq!(reorderable_members, 71);
        assert_eq!(
            moved,
            [
                (5, 6),
                (6, 5),
                (32, 33),
                (33, 32),
                (77, 78),
                (78, 77),
                (84, 85),
                (85, 84),
            ]
        );

        for (expected, observed) in atoms.iter().zip(permuted_atoms) {
            if let WindowAtom::GroupBf {
                lazy_product_count,
                members,
                ..
            } = expected
            {
                if *lazy_product_count >= 2 {
                    let by_record = observed
                        .canonical_records
                        .iter()
                        .skip(1)
                        .copied()
                        .zip(observed.members)
                        .collect::<std::collections::BTreeMap<_, _>>();
                    let head = observed.canonical_records[0];
                    for (offset, member) in members.iter().enumerate() {
                        assert_eq!(by_record[&(head + 1 + offset as u16)], *member);
                    }
                }
            }
        }
    }

    #[test]
    fn linear_singleton_policy_is_independent_and_lossless() {
        let (artifact, atoms) = retained();
        let program = encode_compact_program(
            &atoms,
            &artifact,
            CompactPolicy {
                compact_linear_singleton: true,
                ..CompactPolicy::PASSTHROUGH
            },
        )
        .unwrap();
        let decoded = decode_compact_program(&program).unwrap();
        assert!(decoded
            .iter()
            .any(|atom| atom.encoding == AtomEncoding::LinearSingleton));
        assert!(program.words.len() < COMPACT_WORD_CAPACITY);
        for (expected, observed) in atoms.iter().zip(decoded) {
            if let WindowAtom::Term(term) = expected {
                assert_eq!(observed.members, [*term]);
            }
        }
    }

    #[test]
    fn all_nine_infinity_classes_finish_at_the_declared_cursor() {
        let program = direct();
        for x0 in 0..3 {
            for x1 in 0..3 {
                let (cursor, executed_products, skipped_members) =
                    infinity_cursor_trace(&program, x0, x1).unwrap();
                assert_eq!(cursor, program.words.len());
                if x0 == 2 || x1 == 2 {
                    assert_eq!(executed_products, 82);
                    assert!(skipped_members != 0);
                } else {
                    assert_eq!(executed_products, 0);
                    assert_eq!(skipped_members, 0);
                }
            }
        }
    }

    #[test]
    fn retained_prefix_distribution_and_tail_are_pinned() {
        let (_, atoms) = retained();
        let prefixes = atoms
            .iter()
            .filter_map(|atom| match atom {
                crate::artifact::WindowAtom::GroupBf {
                    lazy_product_count, ..
                } if *lazy_product_count >= 2 => Some(*lazy_product_count),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(prefixes, [6, 14, 10, 17, 4, 4, 3, 3, 7, 4]);
        assert_eq!(
            prefixes
                .iter()
                .map(|value| usize::from(*value))
                .sum::<usize>(),
            72
        );
    }

    #[test]
    fn overflow_is_typed_and_never_truncated() {
        let (artifact, atoms) = retained();
        let mut oversized = artifact.clone();
        oversized.program.extend(artifact.program.iter().copied());
        oversized.record_count = oversized.program.len() as u32;
        let mut oversized_atoms = atoms.clone();
        oversized_atoms.extend(atoms);
        assert!(matches!(
            encode_compact_program(&oversized_atoms, &oversized, CompactPolicy::PASSTHROUGH),
            Err(CompactError::ReservedRegionOverflow {
                maximum: COMPACT_WORD_CAPACITY,
                ..
            })
        ));
    }

    #[test]
    fn rejects_wrong_total_span() {
        let mut program = direct();
        let atom = first_compact(&program);
        let span = (program.words[atom + 1] & ATOM_SPAN_MASK) + 2;
        program.words[atom + 1] =
            (program.words[atom + 1] & !ATOM_SPAN_MASK) | (span & ATOM_SPAN_MASK);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::WrongTotalSpan { .. })
        ));
    }

    #[test]
    fn rejects_wrong_tail_span() {
        let mut program = direct();
        let (atom, _) = atom_starts(&program)
            .into_iter()
            .find(|(_, atom)| atom.encoding == AtomEncoding::Compact && atom.tail_word_span != 0)
            .unwrap();
        let tail = ((program.words[atom + 1] >> ATOM_TAIL_SHIFT) & ATOM_SPAN_MASK) + 1;
        program.words[atom + 1] = (program.words[atom + 1] & !(ATOM_SPAN_MASK << ATOM_TAIL_SHIFT))
            | ((tail & ATOM_SPAN_MASK) << ATOM_TAIL_SHIFT);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::WrongTailSpan { .. })
        ));
    }

    #[test]
    fn rejects_passthrough_arity_disagreement() {
        let mut program = passthrough();
        let mut word = 0usize;
        while program.words[word] as u16 != WindowClass::GroupBf as u16 {
            word += 2;
        }
        program.words[word + 1] = (program.words[word + 1] & 0xffff_0000) | u32::from(u16::MAX);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::PassthroughArityMismatch { .. })
        ));
    }

    #[test]
    fn rejects_bf_e4_crossing() {
        let mut program = direct();
        program.bf_word_count = 0;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::BfE4Crossing { .. })
        ));
    }

    #[test]
    fn rejects_atom_crossing() {
        let mut program = direct();
        let atom = first_compact(&program);
        program.words[atom + 1] = (program.words[atom + 1] & !ATOM_SPAN_MASK) | ATOM_SPAN_MASK;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::AtomCrossing { .. })
        ));
    }

    #[test]
    fn rejects_five_product_legacy_segment() {
        let mut program = passthrough();
        let mut word = 0usize;
        loop {
            let class = program.words[word] as u16;
            let source_b = (program.words[word + 1] >> 16) as u16;
            if class == WindowClass::GroupBf as u16
                && source_b & GROUP_PRODUCT_PREFIX_COUNT_MASK > MAX_INNER_PRODUCTS
            {
                break;
            }
            let records =
                if class == WindowClass::GroupBf as u16 || class == WindowClass::GroupE4 as u16 {
                    (program.words[word + 1] as u16) as usize + 1
                } else {
                    1
                };
            word += 2 * records;
        }
        let fourth_member_word = word + 2 * 4;
        let factor = (program.words[fourth_member_word] >> 16) as u16 & !REDUCE_AFTER;
        program.words[fourth_member_word] =
            (program.words[fourth_member_word] & 0xffff) | (u32::from(factor) << 16);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::FiveProductSegment { .. })
        ));
    }

    #[test]
    fn rejects_inconsistent_member_payload_counts() {
        let mut program = direct();
        let block = first_compact(&program) + 2;
        program.words[block] = (program.words[block] & !0xff) | 0;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::MemberPayloadMismatch { .. })
        ));
    }

    #[test]
    fn rejects_escape_payload_under_compact_tag() {
        let mut program = direct();
        let block = first_compact(&program) + 2;
        program.words[block] &= !(TAG_MASK << TAG_SHIFT);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::EscapePayloadUnderCompactTag { .. })
        ));
    }

    #[test]
    fn rejects_truncated_header() {
        let mut program = direct();
        program.words = vec![TAG_COMPACT_ATOM << TAG_SHIFT];
        program.bf_word_count = 0;
        program.canonical_record_count = 0;
        program.slots.clear();
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::TruncatedHeader { .. })
        ));
    }

    #[test]
    fn rejects_truncated_payload() {
        let mut program = direct();
        let block = first_compact(&program) + 2;
        program.words[block] = (program.words[block] & !0xff) | 0xff;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::TruncatedPayload { .. })
        ));
    }

    #[test]
    fn rejects_invalid_coefficient() {
        let mut program = direct();
        let atom = first_compact(&program);
        program.words[atom] =
            (program.words[atom] & !(0x7f << ATOM_CORE_SHIFT)) | (0x7f << ATOM_CORE_SHIFT);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::InvalidCoefficient { .. })
        ));
    }

    #[test]
    fn rejects_invalid_immediate() {
        let mut program = direct();
        let block = first_compact(&program) + 2;
        program.words[block] = (program.words[block] & !(0x7f << BLOCK_IMMEDIATE_SHIFT))
            | (0x7f << BLOCK_IMMEDIATE_SHIFT);
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::InvalidImmediate { .. })
        ));
    }

    #[test]
    fn rejects_missing_canonical_record() {
        let mut program = direct();
        let block = first_compact(&program) + 2;
        program.words[block + 1] += 1 << BLOCK_CANONICAL_SHIFT;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::MissingCanonicalRecord { .. })
        ));
    }

    #[test]
    fn rejects_duplicate_canonical_record() {
        let mut program = direct();
        program.slots[1].canonical_record = program.slots[0].canonical_record;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::DuplicateCanonicalRecord { .. })
        ));
    }

    #[test]
    fn rejects_nonzero_reserved_bits() {
        let mut program = direct();
        let atom = first_compact(&program);
        program.words[atom] |= 1;
        assert!(matches!(
            decode_compact_program(&program),
            Err(CompactError::NonzeroReservedBits { .. })
        ));
    }
}
