//! Deals complete continuation atoms across the eight MAIN-tail warps.

use super::common::lean::{validate_program, LeanAtom, LeanTerm, LEAN_WORDS_PER_TERM};
use super::common::limits::{
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES, LEAN_MAX_SOURCES, MAX_COEFFICIENT_ENCODINGS,
};
use super::{CoefficientRecipeId, ContinuationLayerProgram, ImmediateId};

pub const MAIN_TAIL_K: usize = 8;
pub const MAIN_TAIL_LIST_OFFSETS: usize = MAIN_TAIL_K + 1;

/// One layer's round-invariant continuation program, dealt for eight warps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainTailProgram {
    pub layer: usize,
    pub list_offsets: [u16; MAIN_TAIL_LIST_OFFSETS],
    pub program_words: Vec<u16>,
    pub immediates: Vec<u32>,
    pub source_count: u16,
    pub c_init_coeff_id: u16,
}

fn member_work(term: &LeanTerm) -> u64 {
    let (body, arity) = match term.class {
        0 => (1, 1),
        1 => (8, 2),
        _ => unreachable!("validated continuation class"),
    };
    body + if term.coeff >= ImmediateId::RESERVED {
        arity
    } else {
        0
    }
}

fn atom_work(atom: &LeanAtom) -> u64 {
    match atom {
        LeanAtom::Term(term) => match term.class {
            0 => 2,
            1 => 10,
            _ => unreachable!("validated continuation class"),
        },
        LeanAtom::Group {
            has_c0,
            has_c2,
            members,
            ..
        } => {
            members.iter().map(member_work).sum::<u64>()
                + 2 * (u64::from(*has_c0) + u64::from(*has_c2))
        }
    }
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

pub fn lower_main_tail_program(program: &ContinuationLayerProgram) -> MainTailProgram {
    let program_words = program.program.words.len();
    assert!(program_words <= LEAN_DESCRIPTOR_PROGRAM_WORDS);
    assert!(program.coefficients.immediates.len() <= LEAN_MAX_IMMEDIATES);
    let source_count = program.coefficients.sources.len();
    assert!(source_count <= LEAN_MAX_SOURCES);
    let coefficient_count =
        CoefficientRecipeId::RESERVED as usize + program.coefficients.coefficients.len();
    assert!(coefficient_count <= MAX_COEFFICIENT_ENCODINGS);
    let c_init_coeff_id = program.coefficients.c_init.map_or(u16::MAX, |id| {
        assert!((id.0 as usize) < coefficient_count);
        u16::try_from(id.0).expect("coefficient IDs must fit u16")
    });
    let atoms = validate_program(&program.program, &program.coefficients).unwrap();
    let costs: Vec<_> = atoms.iter().map(atom_work).collect();
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
        immediates: program.coefficients.immediates.clone(),
        source_count: u16::try_from(source_count).expect("the fixed tail source capacity fits u16"),
        c_init_coeff_id,
    }
}
