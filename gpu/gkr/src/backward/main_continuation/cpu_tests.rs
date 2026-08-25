use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    CoeffTerm, CoefficientRecipeId, ImmediateId, MainContinuationWindowProgram,
    MainContinuationWindowShape,
};

use super::{continuation_window_tensor_reference, ContinuationWindowReferenceError};
use crate::backward::window::reference::tensor_round_tail_reference;
use crate::upstream::{Field, FieldExtension, PrimeField};

const INERT_TAIL_CELL: usize = 13;

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

struct Rng(u64);

impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = splitmix64(self.0);
        (self.0 >> 32) as u32
    }

    fn next_e4(&mut self) -> E4 {
        E4::from_array_of_base(core::array::from_fn(|_| {
            BF::from_u32_with_reduction(self.next_u32())
        }))
    }
}

fn lift(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

fn add(mut left: E4, right: E4) -> E4 {
    left.add_assign(&right);
    left
}

fn mul(mut left: E4, right: E4) -> E4 {
    left.mul_assign(&right);
    left
}

fn neg(mut value: E4) -> E4 {
    value.negate();
    value
}

fn eq_factor(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        add(E4::ONE, neg(coordinate))
    } else {
        coordinate
    }
}

/// Build only the equality table for the current pass's logical-row suffix.
/// No preceding window's table or drained state participates.
fn fresh_suffix_eq(point: &[E4]) -> Vec<E4> {
    (0..(1usize << point.len()))
        .map(|row| {
            point
                .iter()
                .enumerate()
                .fold(E4::ONE, |weight, (bit, coordinate)| {
                    mul(weight, eq_factor((row >> bit) & 1, *coordinate))
                })
        })
        .collect()
}

fn inputs(
    program: &MainContinuationWindowProgram,
    seed: u64,
) -> (Vec<Vec<[E4; 8]>>, Vec<E4>, Vec<E4>) {
    let mut rng = Rng(seed);
    let suffix_point = [rng.next_e4(), rng.next_e4()];
    let eq_suffix = fresh_suffix_eq(&suffix_point);
    let source_rows = (0..program.sources.len())
        .map(|_| {
            (0..eq_suffix.len())
                .map(|_| core::array::from_fn(|_| rng.next_e4()))
                .collect()
        })
        .collect();
    let mut coefficient_bank = (0..program.capacities.coefficient_bank_slots)
        .map(|_| rng.next_e4())
        .collect::<Vec<_>>();
    coefficient_bank[CoefficientRecipeId::ONE.0 as usize] = E4::ONE;
    coefficient_bank[CoefficientRecipeId::NEG_ONE.0 as usize] = neg(E4::ONE);
    (source_rows, coefficient_bank, eq_suffix)
}

fn direct_basis(coordinate: usize, bit: usize) -> E4 {
    match (coordinate, bit) {
        (0, 0) | (1, 1) | (2, 1) => E4::ONE,
        (0, 1) | (1, 0) => E4::ZERO,
        (2, 0) => neg(E4::ONE),
        _ => unreachable!("a ternary coordinate and Boolean bit"),
    }
}

/// Independently evaluate the multilinear polynomial at one tensor cell.
/// Unlike the production oracle, this does not fill Boolean positions and run
/// three in-place difference passes.
fn direct_grid_cell(corners: &[E4; 8], cell: usize) -> E4 {
    let coordinates = [cell / 9, (cell / 3) % 3, cell % 3];
    let mut value = E4::ZERO;
    for (corner, corner_value) in corners.iter().enumerate() {
        let mut weight = E4::ONE;
        for (axis, coordinate) in coordinates.iter().enumerate() {
            weight.mul_assign(&direct_basis(*coordinate, (corner >> axis) & 1));
        }
        weight.mul_assign(corner_value);
        value.add_assign(&weight);
    }
    value
}

fn is_boolean(cell: usize) -> bool {
    cell / 9 < 2 && (cell / 3) % 3 < 2 && cell % 3 < 2
}

fn direct_coefficient(bank: &[E4], id: CoefficientRecipeId) -> E4 {
    bank[id.0 as usize]
}

fn direct_immediate(program: &MainContinuationWindowProgram, id: ImmediateId) -> E4 {
    if id == ImmediateId::ONE {
        E4::ONE
    } else if id == ImmediateId::NEG_ONE {
        neg(E4::ONE)
    } else {
        lift(program.immediates[id.bank_index().unwrap()])
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DirectMutation {
    None,
    R0ProductExcess,
    InfinityLinearLeak,
}

fn direct_term_value(
    term: &CoeffTerm,
    grids: &[[E4; 27]],
    cell: usize,
    mutation: DirectMutation,
) -> E4 {
    match term {
        CoeffTerm::C0Linear { value, .. } => {
            if is_boolean(cell) || (mutation == DirectMutation::InfinityLinearLeak && cell == 2) {
                grids[value.source.0 as usize][cell]
            } else {
                E4::ZERO
            }
        }
        CoeffTerm::DualProduct { lhs, rhs, .. } => {
            // This is the landed R0 excess rule: Boolean products are already
            // materialized and the explicit record contributes only to a cell
            // with at least one infinity coordinate. Continuation must not use it.
            if mutation == DirectMutation::R0ProductExcess && is_boolean(cell) {
                E4::ZERO
            } else {
                mul(grids[lhs.0 as usize][cell], grids[rhs.0 as usize][cell])
            }
        }
        CoeffTerm::C2Product { .. } => {
            panic!("continuation lowering must contain no standalone C2 product")
        }
    }
}

/// Independent semantic evaluator: it walks the compiler's `CoeffLayer` terms
/// and groups, never the lowered plain/product/group record vectors used by
/// `continuation_window_tensor_reference`.
fn direct_tensor(
    program: &MainContinuationWindowProgram,
    source_rows: &[Vec<[E4; 8]>],
    coefficient_bank: &[E4],
    eq_suffix: &[E4],
    mutation: DirectMutation,
) -> [E4; 27] {
    let layer = &program.coefficients;
    let mut grouped = vec![false; layer.terms.len()];
    for group in &layer.groups {
        for member in &group.members {
            grouped[member.term.0 as usize] = true;
        }
    }

    let mut tensor = [E4::ZERO; 27];
    let mut grids = vec![[E4::ZERO; 27]; source_rows.len()];
    for (row, eq_weight) in eq_suffix.iter().enumerate() {
        for source in 0..source_rows.len() {
            grids[source] =
                core::array::from_fn(|cell| direct_grid_cell(&source_rows[source][row], cell));
        }
        for cell in 0..27 {
            let linear_live =
                is_boolean(cell) || (mutation == DirectMutation::InfinityLinearLeak && cell == 2);
            let mut value = if linear_live {
                layer
                    .c_init
                    .map(|id| direct_coefficient(coefficient_bank, id))
                    .unwrap_or(E4::ZERO)
            } else {
                E4::ZERO
            };

            for (term_index, term) in layer.terms.iter().enumerate() {
                if grouped[term_index] {
                    continue;
                }
                let mut contribution = direct_term_value(term, &grids, cell, mutation);
                contribution.mul_assign(&direct_coefficient(coefficient_bank, term.coefficient()));
                value.add_assign(&contribution);
            }
            for group in &layer.groups {
                let mut sum = E4::ZERO;
                for member in &group.members {
                    let mut contribution = direct_term_value(
                        &layer.terms[member.term.0 as usize],
                        &grids,
                        cell,
                        mutation,
                    );
                    contribution.mul_assign(&direct_immediate(program, member.immediate));
                    sum.add_assign(&contribution);
                }
                sum.mul_assign(&direct_coefficient(coefficient_bank, group.core));
                value.add_assign(&sum);
            }
            value.mul_assign(eq_weight);
            tensor[cell].add_assign(&value);
        }
    }
    tensor
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TranscriptObservation {
    coefficients: [E4; 12],
    challenges: [E4; 3],
    seed: [u32; 8],
    claim: E4,
    eq_prefactor: E4,
}

fn observe_transcript(tensor: [E4; 27]) -> TranscriptObservation {
    let rho = [lift(3), lift(5), lift(7)];
    let mut seed = [
        0x1020_3040,
        0x5060_7080,
        0x90a0_b0c0,
        0xd0e0_f001,
        0x1234_5678,
        0x9abc_def0,
        0x0bad_cafe,
        0xfeed_beef,
    ];
    let mut claim = lift(11);
    let mut eq_prefactor = lift(13);
    let (coefficients, challenges) =
        tensor_round_tail_reference(tensor, &rho, &mut seed, &mut claim, &mut eq_prefactor);
    TranscriptObservation {
        coefficients,
        challenges,
        seed,
        claim,
        eq_prefactor,
    }
}

fn transpose_x0_x2(tensor: [E4; 27]) -> [E4; 27] {
    let mut transposed = [E4::ZERO; 27];
    for x2 in 0..3 {
        for x1 in 0..3 {
            for x0 in 0..3 {
                transposed[9 * x2 + 3 * x1 + x0] = tensor[9 * x0 + 3 * x1 + x2];
            }
        }
    }
    transposed
}

fn mutation_fixture() -> (
    MainContinuationWindowProgram,
    Vec<Vec<[E4; 8]>>,
    Vec<E4>,
    Vec<E4>,
) {
    let (programs, _) =
        crate::backward::compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
    let bundle = programs
        .resolve_main_continuation_window_programs()
        .expect("the committed corpus lowers");
    let program = bundle
        .layers
        .iter()
        .find(|program| {
            program.shape == MainContinuationWindowShape::UNIVERSAL
                && !program.dual_products.is_empty()
                && !program.plain_linear.is_empty()
                && !program.grouped_records.is_empty()
                && program.c_init.is_some()
        })
        .expect("the corpus contains a fixture exercising all continuation classes")
        .clone();
    let (source_rows, coefficient_bank, eq_suffix) = inputs(&program, 0xdec0_de01_0305_0709);
    (program, source_rows, coefficient_bank, eq_suffix)
}

#[test]
fn cpu_main_continuation_reference_matches_one_row_direct_model() {
    let (program, _, _, _) = mutation_fixture();
    assert_eq!(program.shape, MainContinuationWindowShape::UNIVERSAL);

    // Deliberately tiny and nonrandom: one logical row, Eq = [1], one
    // eight-corner affine sequence per dense semantic source, and a scalar
    // sequence for the coefficient bank.
    let eq_suffix = vec![E4::ONE];
    let source_rows = (0..program.sources.len())
        .map(|source| {
            vec![core::array::from_fn(|corner| {
                lift(17 + 11 * source as u32 + 3 * corner as u32)
            })]
        })
        .collect::<Vec<_>>();
    let mut coefficient_bank = (0..program.capacities.coefficient_bank_slots)
        .map(|slot| lift(101 + 7 * slot as u32))
        .collect::<Vec<_>>();
    coefficient_bank[CoefficientRecipeId::ONE.0 as usize] = E4::ONE;
    coefficient_bank[CoefficientRecipeId::NEG_ONE.0 as usize] = neg(E4::ONE);

    assert_eq!(eq_suffix.len(), 1, "the direct model has one logical row");
    assert!(
        source_rows.iter().all(|rows| rows.len() == 1),
        "every semantic source has exactly one eight-corner row",
    );

    let expected = direct_tensor(
        &program,
        &source_rows,
        &coefficient_bank,
        &eq_suffix,
        DirectMutation::None,
    );
    let actual =
        continuation_window_tensor_reference(&program, &source_rows, &coefficient_bank, &eq_suffix)
            .expect("the deterministic one-row model is well-shaped");
    assert_eq!(actual, expected);
    assert_eq!(observe_transcript(actual), observe_transcript(expected));
}

#[test]
fn cpu_main_continuation_reference_matches_independent_models_on_all_57_coordinates() {
    let mut coordinates = 0usize;
    let mut plain_terms = 0usize;
    let mut dual_terms = 0usize;
    let mut groups = 0usize;
    let mut c_init = 0usize;

    for (layout_index, (layout, _)) in crate::backward::CONTINUATION_GOLDEN_CORPUS
        .iter()
        .enumerate()
    {
        let (programs, layers) = crate::backward::compile_corpus_layout(layout);
        let bundle = programs
            .resolve_main_continuation_window_programs()
            .expect("the committed corpus lowers");
        assert_eq!(bundle.layers.len(), layers);
        for (layer_index, program) in bundle.layers.iter().enumerate() {
            let seed = splitmix64(
                0xc011_ab1e_0000_0000 ^ ((layout_index as u64) << 24) ^ layer_index as u64,
            );
            let (source_rows, coefficient_bank, eq_suffix) = inputs(program, seed);
            let expected = direct_tensor(
                program,
                &source_rows,
                &coefficient_bank,
                &eq_suffix,
                DirectMutation::None,
            );
            let actual = continuation_window_tensor_reference(
                program,
                &source_rows,
                &coefficient_bank,
                &eq_suffix,
            )
            .unwrap_or_else(|error| panic!("{layout}:{layer_index}: {error}"));
            assert_eq!(actual, expected, "{layout}:{layer_index}");

            // The same production transcript oracle independently consumes
            // each tensor through all three scalar transitions.
            assert_eq!(
                observe_transcript(actual),
                observe_transcript(expected),
                "transcript {layout}:{layer_index}",
            );
            coordinates += 1;
            plain_terms += program.plain_linear.len();
            dual_terms += program.dual_products.len();
            groups += program.grouped_records.len();
            c_init += usize::from(program.c_init.is_some());
        }
    }

    assert_eq!(
        coordinates, 57,
        "the full retained corpus must be exercised"
    );
    assert!(
        plain_terms > 0,
        "the corpus must reach Boolean-only linear terms"
    );
    assert!(dual_terms > 0, "the corpus must reach full dual products");
    assert!(groups > 0, "the corpus must reach grouped execution");
    assert!(c_init > 0, "the corpus must reach Boolean-only c_init");
}

#[test]
fn cpu_main_continuation_reference_convention_mutations_are_live() {
    let (program, source_rows, coefficient_bank, eq_suffix) = mutation_fixture();
    let correct =
        continuation_window_tensor_reference(&program, &source_rows, &coefficient_bank, &eq_suffix)
            .unwrap();
    let correct_observation = observe_transcript(correct);

    assert_ne!(
        observe_transcript(transpose_x0_x2(correct)),
        correct_observation,
        "transposing the low stride-nine axis with x0 must be observable",
    );

    let r0_excess = direct_tensor(
        &program,
        &source_rows,
        &coefficient_bank,
        &eq_suffix,
        DirectMutation::R0ProductExcess,
    );
    assert_ne!(
        observe_transcript(r0_excess),
        correct_observation,
        "continuation DualProduct must be full at Boolean cells, not R0 excess",
    );

    let infinity_leak = direct_tensor(
        &program,
        &source_rows,
        &coefficient_bank,
        &eq_suffix,
        DirectMutation::InfinityLinearLeak,
    );
    assert_ne!(
        observe_transcript(infinity_leak),
        correct_observation,
        "linear and c_init contributions must not leak into infinity cells",
    );

    let consumed_lane = usize::from(program.dual_products[0].source_a);
    let destination = &program.sources[consumed_lane];
    let donor = program
        .sources
        .iter()
        .find(|source| source.id != destination.id)
        .expect("the fixture has multiple semantic SourceId lanes");
    let destination_lane = destination.id.0 as usize;
    let donor_lane = donor.id.0 as usize;
    assert_eq!(
        usize::from(destination.publish_column),
        destination_lane,
        "the consumed semantic SourceId has its canonical dense lane",
    );
    assert_eq!(
        usize::from(donor.publish_column),
        donor_lane,
        "the donor semantic SourceId has its canonical dense lane",
    );
    assert_ne!(
        destination.id, donor.id,
        "the mispublication must cross distinct semantic SourceId lanes",
    );

    let mut source_id_mispublication = source_rows.clone();
    source_id_mispublication[destination_lane] = source_rows[donor_lane].clone();
    let mispublished_tensor = continuation_window_tensor_reference(
        &program,
        &source_id_mispublication,
        &coefficient_bank,
        &eq_suffix,
    )
    .unwrap();
    assert_ne!(
        observe_transcript(mispublished_tensor),
        correct_observation,
        "mispublishing a donor semantic SourceId under the consumed destination SourceId lane must change the transcript",
    );

    let mut inert_mutant = correct;
    inert_mutant[INERT_TAIL_CELL].add_assign(&E4::ONE);
    assert_eq!(
        observe_transcript(inert_mutant),
        correct_observation,
        "cell 13 feeds only at-one evaluations reconstructed from the claim",
    );

    let mut live_mutant = correct;
    live_mutant[0].add_assign(&E4::ONE);
    assert_ne!(
        observe_transcript(live_mutant),
        correct_observation,
        "a live tensor cell mutation must change the three-round transcript",
    );
}

#[test]
fn cpu_main_continuation_reference_rejects_noncanonical_or_misshaped_inputs() {
    let (program, source_rows, coefficient_bank, eq_suffix) = mutation_fixture();
    let mut noncanonical = program.clone();
    noncanonical.sources[0].publish_column = 1;
    assert!(matches!(
        continuation_window_tensor_reference(
            &noncanonical,
            &source_rows,
            &coefficient_bank,
            &eq_suffix,
        ),
        Err(ContinuationWindowReferenceError::NonCanonicalPublication { source: 0, .. })
    ));

    let mut short_rows = source_rows.clone();
    short_rows[0].pop();
    assert!(matches!(
        continuation_window_tensor_reference(&program, &short_rows, &coefficient_bank, &eq_suffix,),
        Err(ContinuationWindowReferenceError::SourceRowCount { source: 0, .. })
    ));

    assert_eq!(
        continuation_window_tensor_reference(&program, &source_rows, &coefficient_bank, &[]),
        Err(ContinuationWindowReferenceError::EmptySuffixEq),
    );
}

#[test]
fn cpu_task8_differential_is_standalone_from_prove() {
    let crate_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    fn rust_sources(root: &std::path::Path, output: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(root)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", root.display()))
        {
            let path = entry
                .expect("source-directory entry must be readable")
                .path();
            if path.is_dir() {
                rust_sources(&path, output);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                output.push(path);
            }
        }
    }

    let mut production_sources = Vec::new();
    rust_sources(
        &crate_root.join("../circuit_prover/src/proof"),
        &mut production_sources,
    );
    rust_sources(&crate_root.join("src/backward"), &mut production_sources);
    let standalone_only = [
        crate_root.join("src/backward/main_continuation/cpu_tests.rs"),
        crate_root.join("src/backward/main_continuation/differential_tests.rs"),
        crate_root.join("src/backward/main_continuation/tests.rs"),
    ];
    production_sources.retain(|path| !standalone_only.contains(path));
    production_sources.sort();
    assert!(
        production_sources.len() > 20,
        "the prove/backward source census unexpectedly collapsed"
    );
    let forbidden = [
        "task8_continuation_differential_test",
        "task8_",
        "Task8",
        "Task 8",
        "schedule_prepared_main_continuation_differential",
        "requesting_main_continuation_differential",
        "prove_main_continuation_differential",
        "task8_enqueue_scope!",
        "task8_register_symbol",
        "task8_register_descriptor_sources",
        "Task8MainContinuationLaunchCounterGuard::install",
    ];

    for path in production_sources {
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        for needle in forbidden {
            assert!(
                !source.contains(needle),
                "Task 8 differential instrumentation `{needle}` remains in prove-transitive source {}",
                path.display(),
            );
        }
    }

    let module_source =
        std::fs::read_to_string(crate_root.join("src/backward/main_continuation/mod.rs"))
            .expect("main-continuation module source must be readable");
    assert!(
        module_source.contains("#[cfg(test)]\nmod differential_tests;"),
        "the Task 8 differential model must compile only as standalone test code",
    );
    assert!(
        module_source.contains("#[cfg(all(test, not(no_cuda)))]\nmod tests;"),
        "the standalone GPU component harness must remain test-only",
    );
    let standalone_source =
        std::fs::read_to_string(crate_root.join("src/backward/main_continuation/tests.rs"))
            .expect("standalone main-continuation test source must be readable");
    for required in [
        "fn main_continuation_standalone_differential_gpu_oracle()",
        "bind_first_main_continuation_window(",
        "bind_later_main_continuation_window(",
        "launch_main_continuation_window(",
        "launch_window_tensor_round_tail(",
        "memory_copy_async(",
        "Callbacks::new()",
        ".schedule(",
    ] {
        assert!(
            standalone_source.contains(required),
            "standalone component harness lost `{required}`",
        );
    }
}
