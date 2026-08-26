//! Static lowering for the main-layer tail block.
//!
//! The tail reuses the continuation lean wire. Its only program transform is a
//! deterministic eight-way deal of complete atoms; source addressing disappears
//! because the continuation producer publishes dense E4 columns in `SourceId`
//! order.

use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::{
    category_arity, decode_continuation_program, CoefficientRecipeId, ContinuationLayerProgram,
    ImmediateId, LeanAtom, LeanCodecError, LeanTerm, SourceId, TermCategory, LEAN_CONT_OPCODES,
    LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_GROUP_FLAG_C0,
    LEAN_GROUP_FLAG_C2, LEAN_MAX_IMMEDIATES, LEAN_WORDS_PER_TERM, MAX_BACKWARD_SOURCES,
    MAX_COEFFICIENT_ENCODINGS, SOURCE_NONE,
};

pub(crate) const MAIN_TAIL_K: usize = 8;
pub(crate) const MAIN_TAIL_LIST_OFFSETS: usize = MAIN_TAIL_K + 1;
pub(crate) const MAIN_TAIL_LIST_OFFSETS_OFFSET: usize = 0;
pub(crate) const MAIN_TAIL_PROGRAM_OFFSET: usize =
    MAIN_TAIL_LIST_OFFSETS_OFFSET + MAIN_TAIL_LIST_OFFSETS * size_of::<u16>();
pub(crate) const MAIN_TAIL_PROGRAM_WORD_CAPACITY: usize = LEAN_DESCRIPTOR_PROGRAM_WORDS;
pub(crate) const MAIN_TAIL_PROGRAM_BYTES: usize = LEAN_DESCRIPTOR_PROGRAM_BYTES;
pub(crate) const MAIN_TAIL_IMMEDIATE_OFFSET: usize =
    (MAIN_TAIL_PROGRAM_OFFSET + MAIN_TAIL_PROGRAM_BYTES).next_multiple_of(size_of::<u32>());
pub(crate) const MAIN_TAIL_IMMEDIATE_CAPACITY: usize = LEAN_MAX_IMMEDIATES;
pub(crate) const MAIN_TAIL_IMMEDIATE_BYTES: usize = MAIN_TAIL_IMMEDIATE_CAPACITY * size_of::<u32>();
pub(crate) const MAIN_TAIL_BLOB_ALIGNMENT: usize = 16;
pub(crate) const MAIN_TAIL_BLOB_BYTES: usize = (MAIN_TAIL_IMMEDIATE_OFFSET
    + MAIN_TAIL_IMMEDIATE_BYTES)
    .next_multiple_of(MAIN_TAIL_BLOB_ALIGNMENT);
pub(crate) const MAIN_TAIL_SOURCE_CAPACITY: usize = MAX_BACKWARD_SOURCES;
pub(crate) const MAIN_TAIL_C_INIT_NONE: u16 = u16::MAX;

const _: () = {
    assert!(MAIN_TAIL_LIST_OFFSETS_OFFSET == 0);
    assert!(MAIN_TAIL_PROGRAM_OFFSET == 18);
    assert!(MAIN_TAIL_PROGRAM_WORD_CAPACITY == 6_472);
    assert!(MAIN_TAIL_PROGRAM_BYTES == 12_944);
    assert!(MAIN_TAIL_IMMEDIATE_OFFSET == 12_964);
    assert!(MAIN_TAIL_IMMEDIATE_CAPACITY == 512);
    assert!(MAIN_TAIL_BLOB_BYTES == 15_024);
    assert!(MAIN_TAIL_BLOB_BYTES.is_multiple_of(MAIN_TAIL_BLOB_ALIGNMENT));
    assert!(MAIN_TAIL_SOURCE_CAPACITY == 1_072);
};

/// One layer's round-invariant continuation program, dealt for eight warps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainTailProgram {
    pub layer: usize,
    pub list_offsets: [u16; MAIN_TAIL_LIST_OFFSETS],
    pub program_words: Vec<u16>,
    pub immediates: Vec<u32>,
    pub source_count: u16,
    pub coefficient_count: u16,
    pub c_init_coeff_id: u16,
}

fn continuation_category(record: usize, term: &LeanTerm) -> Result<TermCategory, LeanCodecError> {
    LEAN_CONT_OPCODES
        .iter()
        .find(|(class, _)| *class == u16::from(term.class))
        .map(|(_, category)| *category)
        .ok_or(LeanCodecError::ClassNotInRegime {
            term: record,
            opcode: u16::from(term.class),
        })
}

fn validate_sources(
    record: usize,
    term: &LeanTerm,
    category: TermCategory,
    source_count: usize,
) -> Result<(), LeanCodecError> {
    let source = |slot: u16| -> Result<(), LeanCodecError> {
        if usize::from(slot) >= source_count {
            return Err(LeanCodecError::SourceOutOfRange { term: record, slot });
        }
        Ok(())
    };
    source(term.source_a)?;
    if category_arity(category) == 1 {
        if term.source_b != SOURCE_NONE {
            return Err(LeanCodecError::SourceBMustBeNone { term: record });
        }
    } else if term.source_b == SOURCE_NONE {
        return Err(LeanCodecError::SourceBMissing { term: record });
    } else {
        source(term.source_b)?;
    }
    Ok(())
}

fn validate_recipe(
    record: usize,
    coefficient: u16,
    coefficient_count: usize,
) -> Result<(), LeanCodecError> {
    if usize::from(coefficient) >= coefficient_count {
        return Err(LeanCodecError::CoefficientOutOfRange {
            term: record,
            coeff: coefficient,
        });
    }
    Ok(())
}

fn validate_immediate(
    record: usize,
    immediate: u16,
    immediate_count: usize,
) -> Result<(), LeanCodecError> {
    let limit = usize::from(ImmediateId::RESERVED) + immediate_count;
    if usize::from(immediate) >= limit {
        return Err(LeanCodecError::ImmediateOutOfRange {
            term: record,
            id: immediate,
        });
    }
    Ok(())
}

fn category_flags(category: TermCategory) -> u16 {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => LEAN_GROUP_FLAG_C0,
        TermCategory::C2ProductBfBf | TermCategory::C2ProductBfE4 | TermCategory::C2ProductE4E4 => {
            LEAN_GROUP_FLAG_C2
        }
        TermCategory::DualProductE4 => LEAN_GROUP_FLAG_C0 | LEAN_GROUP_FLAG_C2,
    }
}

fn singleton_work(category: TermCategory) -> u64 {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => 2,
        TermCategory::C2ProductBfBf | TermCategory::C2ProductBfE4 | TermCategory::C2ProductE4E4 => {
            6
        }
        TermCategory::DualProductE4 => 10,
    }
}

fn member_work(category: TermCategory, immediate: u16) -> u64 {
    let body = match category {
        TermCategory::C0LinearE4 => 1,
        TermCategory::DualProductE4 => 8,
        other => singleton_work(other),
    };
    let immediate_surcharge = if immediate < ImmediateId::RESERVED {
        0
    } else {
        category_arity(category) as u64
    };
    body + immediate_surcharge
}

fn validate_and_cost_atoms(
    atoms: &[LeanAtom],
    coefficient_count: usize,
    immediate_count: usize,
    source_count: usize,
) -> Vec<u64> {
    let mut costs = Vec::with_capacity(atoms.len());
    let mut record = 0usize;
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                let category = continuation_category(record, term).unwrap();
                validate_recipe(record, term.coeff, coefficient_count).unwrap();
                validate_sources(record, term, category, source_count).unwrap();
                costs.push(singleton_work(category));
                record += 1;
            }
            LeanAtom::Group {
                core,
                has_c0,
                has_c2,
                members,
            } => {
                if CoefficientRecipeId(u32::from(*core)).literal().is_some() {
                    panic!("group core at atom {record} must not be literal");
                }
                validate_recipe(record, *core, coefficient_count).unwrap();
                let header = record;
                let mut expected_flags = 0u16;
                let mut cost = 0u64;
                for (offset, member) in members.iter().enumerate() {
                    let position = header + 1 + offset;
                    let category = continuation_category(position, member).unwrap();
                    validate_immediate(position, member.coeff, immediate_count).unwrap();
                    validate_sources(position, member, category, source_count).unwrap();
                    expected_flags |= category_flags(category);
                    cost += member_work(category, member.coeff);
                }
                let flags = u16::from(*has_c0) | (u16::from(*has_c2) << 1);
                if flags != expected_flags {
                    panic!(
                        "group flags at atom {header} are {flags:#x}, expected {expected_flags:#x}"
                    );
                }
                cost += 2 * (u64::from(*has_c0) + u64::from(*has_c2));
                costs.push(cost);
                record += 1 + members.len();
            }
        }
    }
    costs
}

fn deal_atoms(costs: &[u64]) -> [Vec<usize>; MAIN_TAIL_K] {
    let mut lists: [Vec<usize>; MAIN_TAIL_K] = std::array::from_fn(|_| Vec::new());
    let mut loads = [0u64; MAIN_TAIL_K];
    for (atom, &cost) in costs.iter().enumerate() {
        let target = (0..MAIN_TAIL_K)
            .min_by_key(|&list| (loads[list], list))
            .expect("the main-tail deal has eight lists");
        lists[target].push(atom);
        loads[target] += cost.max(1);
    }
    lists
}

fn validate_canonical_sources(program: &ContinuationLayerProgram) -> usize {
    let semantic = program.coefficients.sources.len();
    let bound = program.binding.source_slots.len();
    let required = semantic.max(bound);
    assert!(required <= MAIN_TAIL_SOURCE_CAPACITY);
    assert!(!program.binding.windows.is_empty());
    assert_eq!(semantic, bound);

    for (source, semantic_source) in program.coefficients.sources.iter().enumerate() {
        assert_eq!(semantic_source.field, FieldKind::Ext);
        let slot = &program.binding.source_slots[source];
        let found = program
            .binding
            .resolve(slot.window, slot.column)
            .expect("every bound source must resolve");
        assert_eq!(found, SourceId(source as u32));
    }

    let columns: usize = program
        .binding
        .windows
        .iter()
        .map(|window| window.columns.len())
        .sum();
    assert_eq!(columns, semantic);
    let mut seen = vec![false; semantic];
    for window in &program.binding.windows {
        for column in &window.columns {
            let source = column.source as usize;
            let was_seen = seen.get_mut(source).expect("source index must be in range");
            assert!(!*was_seen);
            *was_seen = true;
        }
    }
    debug_assert!(seen.into_iter().all(|source| source));
    semantic
}

/// Lower one continuation layer into the round-invariant tail representation.
pub(crate) fn lower_main_tail_program(program: &ContinuationLayerProgram) -> MainTailProgram {
    let program_words = program.program.words.len();
    assert!(program_words <= MAIN_TAIL_PROGRAM_WORD_CAPACITY);
    let immediate_count = program.immediates.len();
    assert!(immediate_count <= MAIN_TAIL_IMMEDIATE_CAPACITY);
    let source_count = validate_canonical_sources(program);
    let coefficient_count =
        CoefficientRecipeId::RESERVED as usize + program.coefficient_recipes.len();
    assert!(coefficient_count <= MAX_COEFFICIENT_ENCODINGS);
    let c_init_coeff_id = match program.c_init {
        None => MAIN_TAIL_C_INIT_NONE,
        Some(id) => {
            assert!((id.0 as usize) < coefficient_count);
            u16::try_from(id.0).expect("coefficient IDs must fit u16")
        }
    };

    let atoms = decode_continuation_program(&program.program).unwrap();
    let costs = validate_and_cost_atoms(&atoms, coefficient_count, immediate_count, source_count);
    let lists = deal_atoms(&costs);

    let mut spans = Vec::with_capacity(atoms.len());
    let mut record = 0usize;
    for atom in &atoms {
        let records = match atom {
            LeanAtom::Term(_) => 1,
            LeanAtom::Group { members, .. } => 1 + members.len(),
        };
        spans.push((record * LEAN_WORDS_PER_TERM, records * LEAN_WORDS_PER_TERM));
        record += records;
    }

    let mut dealt_words = Vec::with_capacity(program_words);
    let mut list_offsets = [0u16; MAIN_TAIL_LIST_OFFSETS];
    for (list, atoms) in lists.iter().enumerate() {
        list_offsets[list] = u16::try_from(dealt_words.len())
            .expect("the fixed tail program capacity fits u16 offsets");
        for &atom in atoms {
            let (first, words) = spans[atom];
            dealt_words.extend_from_slice(&program.program.words[first..first + words]);
        }
    }
    list_offsets[MAIN_TAIL_K] =
        u16::try_from(dealt_words.len()).expect("the fixed tail program capacity fits u16 offsets");
    debug_assert_eq!(dealt_words.len(), program_words);

    MainTailProgram {
        layer: program.layer,
        list_offsets,
        program_words: dealt_words,
        immediates: program.immediates.clone(),
        source_count: u16::try_from(source_count).expect("the fixed tail source capacity fits u16"),
        coefficient_count: u16::try_from(coefficient_count)
            .expect("the coefficient encoding capacity fits u16"),
        c_init_coeff_id,
    }
}
