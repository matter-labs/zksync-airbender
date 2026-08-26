use core::mem::{align_of, offset_of, size_of};

use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    interpret_continuation_program, CoeffResolver, CoefficientRecipeId, ContinuationLayerProgram,
    SourceId,
};

use super::reference::{
    main_tail_reference, main_tail_reference_with_mutation, MainTailClaimOutput,
    MainTailReferenceEntry, MainTailReferenceError, MainTailReferenceInput,
    MainTailReferenceMutation, MainTailReferenceOutput,
};
use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::{
    compile_corpus_layout, continuation_golden_path, decode_golden, make_eq_sizes,
};
use crate::upstream::{Field, FieldExtension, PrimeField};

use super::super::binding::{
    serialize_main_tail_program_blob, validate_main_tail_final_publication_capacity,
    MainTailBindError, MainTailDesc, MainTailProgramBlob, MAIN_TAIL_DESCRIPTOR_BYTES,
    MAIN_TAIL_KERNEL_ARGUMENT_BYTES, MAIN_TAIL_PARAMETER_HEADROOM,
};

fn lift(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

fn neg(mut value: E4) -> E4 {
    value.negate();
    value
}

fn eq_weight(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        let mut weight = E4::ONE;
        weight.sub_assign(&coordinate);
        weight
    } else {
        coordinate
    }
}

fn direct_eq(point: &[E4]) -> Vec<E4> {
    (0..1usize << point.len())
        .map(|row| {
            point
                .iter()
                .enumerate()
                .fold(E4::ONE, |mut weight, (bit, coordinate)| {
                    weight.mul_assign(&eq_weight((row >> bit) & 1, *coordinate));
                    weight
                })
        })
        .collect()
}

#[test]
fn cpu_main_tail_d3_fold_uses_generated_challenges_not_previous_claim_coordinates() {
    let source = include_str!("../../../../native/gkr/backward/main_tail.cuh");
    let start = source
        .find("if (threadIdx.x < 3)")
        .expect("main-tail D3 coordinate load must remain present");
    let end = source[start..]
        .find("if (threadIdx.x == 0)")
        .map(|offset| start + offset)
        .expect("main-tail Eq-state initialization must follow the D3 coordinate load");
    let d3_coordinate_load = &source[start..end];

    assert!(
        d3_coordinate_load.contains(
            "d3_coordinates[threadIdx.x] = desc.challenges_out[u32{desc.tail_start} - 3u + threadIdx.x]"
        ),
        "the D3 fold must consume the three generated sumcheck challenges immediately before tail_start"
    );
    assert!(
        !d3_coordinate_load.contains("d3_coordinates[threadIdx.x] = desc.prev_claim_coordinates"),
        "the incoming claim point is only the round-update normalization point, not a source-fold challenge"
    );
}

fn rich_program() -> ContinuationLayerProgram {
    let (programs, layers) = compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
    (0..layers)
        .map(|layer| programs.continuation_layer(layer))
        .find(|program| {
            program.coefficients.sources.len() > 1
                && !program.coefficient_recipes.is_empty()
                && !program.program.words.is_empty()
        })
        .expect("the retained corpus has a continuation layer with live banked coefficients")
        .clone()
}

fn maximum_source_program() -> ContinuationLayerProgram {
    let entries = decode_golden(&std::fs::read(continuation_golden_path()).unwrap()).unwrap();
    let (layout, layer, source_count) = entries
        .iter()
        .flat_map(|entry| {
            entry.dto.rounds.iter().map(move |round| {
                (
                    entry.layout.as_str(),
                    entry.dto.layer as usize,
                    round.sources.len(),
                )
            })
        })
        .max_by_key(|(_, _, source_count)| *source_count)
        .expect("the continuation golden is nonempty");
    assert_eq!(source_count, 1_012);
    let (programs, _) = compile_corpus_layout(layout);
    let program = programs.continuation_layer(layer).clone();
    assert_eq!(program.coefficients.sources.len(), source_count);
    program
}

struct Fixture {
    program: ContinuationLayerProgram,
    tail_program: super::super::MainTailProgram,
    source_ids: Vec<SourceId>,
    columns: Vec<E4>,
    coefficient_bank: Vec<E4>,
    generated_challenges: Vec<E4>,
    claim_coordinates: Vec<E4>,
    entry_eq_low: Vec<E4>,
    seed: [u32; 8],
    claim: E4,
    eq_prefactor: E4,
    entry_round: u8,
    entry_depth: u8,
    eq_boundary: MainEqBoundaryWitness,
    tail_rounds: usize,
}

impl Fixture {
    fn new(program: ContinuationLayerProgram, tail_rounds: usize) -> Self {
        assert!((1..=6).contains(&tail_rounds));
        let tail_program = super::super::lower_main_tail_program(&program).unwrap();
        let source_count = program.coefficients.sources.len();
        let source_ids = (0..source_count)
            .map(|source| SourceId(source as u32))
            .collect::<Vec<_>>();
        let entry_round = 6u8;
        let entry_depth = entry_round - 3;
        let folding_steps = usize::from(entry_round) + tail_rounds;
        let stride = 1usize << (tail_rounds + 3);
        let columns = (0..source_count * stride)
            .map(|index| {
                let source = index / stride;
                let element = index % stride;
                lift(17 + (source as u32).wrapping_mul(65_537) + (element as u32).wrapping_mul(257))
            })
            .collect::<Vec<_>>();
        let mut coefficient_bank = (0..usize::from(tail_program.coefficient_count))
            .map(|index| lift(101 + 19 * index as u32))
            .collect::<Vec<_>>();
        coefficient_bank[CoefficientRecipeId::ONE.0 as usize] = E4::ONE;
        coefficient_bank[CoefficientRecipeId::NEG_ONE.0 as usize] = neg(E4::ONE);
        let claim_coordinates = (0..folding_steps)
            .map(|index| lift(307 + 23 * index as u32))
            .collect::<Vec<_>>();
        let generated_challenges = (0..folding_steps)
            .map(|index| lift(1_307 + 29 * index as u32))
            .collect::<Vec<_>>();
        let semantic_suffix_offset = entry_round + 1;
        let entry_eq_low =
            direct_eq(&claim_coordinates[usize::from(semantic_suffix_offset)..folding_steps]);
        let eq_boundary = MainEqBoundaryWitness {
            consumer_round: entry_round,
            semantic_suffix_offset,
            eq_sizes: make_eq_sizes(tail_rounds - 1),
        };
        Self {
            program,
            tail_program,
            source_ids,
            columns,
            coefficient_bank,
            generated_challenges,
            claim_coordinates,
            entry_eq_low,
            seed: [
                0x1020_3040,
                0x5060_7080,
                0x90a0_b0c0,
                0xd0e0_f001,
                0x1234_5678,
                0x9abc_def0,
                0x0bad_cafe,
                0xfeed_beef,
            ],
            claim: lift(19),
            eq_prefactor: lift(29),
            entry_round,
            entry_depth,
            eq_boundary,
            tail_rounds,
        }
    }

    fn input(&self, claim_output: MainTailClaimOutput) -> MainTailReferenceInput<'_> {
        MainTailReferenceInput {
            program: &self.program,
            tail_program: &self.tail_program,
            coefficient_bank: &self.coefficient_bank,
            entry: MainTailReferenceEntry {
                source_ids: &self.source_ids,
                columns: &self.columns,
                stride: 1usize << (self.tail_rounds + 3),
                depth: self.entry_depth,
            },
            generated_challenges: &self.generated_challenges,
            claim_coordinates: &self.claim_coordinates,
            entry_eq_low: &self.entry_eq_low,
            seed: self.seed,
            claim: self.claim,
            eq_prefactor: self.eq_prefactor,
            entry_round: self.entry_round,
            eq_boundary: self.eq_boundary,
            claim_output,
        }
    }
}

fn assert_same_semantics(left: &MainTailReferenceOutput, right: &MainTailReferenceOutput) {
    assert_eq!(left.rounds, right.rounds);
    assert_eq!(left.seed, right.seed);
    assert_eq!(left.claim, right.claim);
    assert_eq!(left.eq_prefactor, right.eq_prefactor);
    assert_eq!(left.final_eq_low, right.final_eq_low);
    assert_eq!(left.final_eq_sizes, right.final_eq_sizes);
    assert_eq!(
        left.final_semantic_suffix_offset,
        right.final_semantic_suffix_offset
    );
    assert_eq!(left.final_columns, right.final_columns);
    assert_eq!(left.final_stride, right.final_stride);
}

fn direct_d3(fixture: &Fixture, source: usize, output_row: usize) -> E4 {
    let stride = 1usize << (fixture.tail_rounds + 3);
    let input = source * stride + 8 * output_row;
    let coordinates = &fixture.generated_challenges
        [usize::from(fixture.entry_round) - 3..usize::from(fixture.entry_round)];
    (0..8).fold(E4::ZERO, |mut folded, q| {
        let mut weight = E4::ONE;
        for (bit, coordinate) in coordinates.iter().enumerate() {
            weight.mul_assign(&eq_weight((q >> bit) & 1, *coordinate));
        }
        let mut contribution = fixture.columns[input + q];
        contribution.mul_assign(&weight);
        folded.add_assign(&contribution);
        folded
    })
}

#[test]
fn cpu_main_tail_reference_folds_ruled_and_synthetic_tails_to_dense_stride_two() {
    let program = rich_program();
    for tail_rounds in [1usize, 2, 4, 5, 6] {
        let fixture = Fixture::new(program.clone(), tail_rounds);
        let aliased = main_tail_reference(fixture.input(MainTailClaimOutput::Aliased)).unwrap();
        let detached = main_tail_reference(fixture.input(MainTailClaimOutput::Detached)).unwrap();
        assert_same_semantics(&aliased, &detached);

        assert_eq!(aliased.rounds.len(), tail_rounds);
        assert_eq!(aliased.final_stride, 2);
        assert_eq!(
            aliased.final_columns.len(),
            fixture.source_ids.len() * aliased.final_stride
        );
        assert_eq!(aliased.final_eq_low, vec![E4::ONE]);
        assert_eq!(aliased.final_eq_sizes, make_eq_sizes(0));
        assert_eq!(
            aliased.final_semantic_suffix_offset as usize,
            usize::from(fixture.entry_round) + tail_rounds
        );
        for (iteration, round) in aliased.rounds.iter().enumerate() {
            assert_eq!(round.absolute_round, fixture.entry_round + iteration as u8);
            assert_eq!(
                round.semantic_suffix_offset,
                fixture.entry_round + 1 + iteration as u8
            );
            assert_eq!(round.eq_sizes, make_eq_sizes(tail_rounds - iteration - 1));
            assert_eq!(
                round.evaluation_rows,
                1usize << (tail_rounds - iteration - 1)
            );
            assert_eq!(
                aliased.claim_coordinates[usize::from(round.absolute_round)],
                round.challenge,
                "the aliasing path must publish only after reading the old coordinate",
            );
        }
        assert_eq!(
            detached.claim_coordinates, fixture.claim_coordinates,
            "the detached challenge output must not overwrite the input point",
        );

        if tail_rounds == 1 {
            for source in 0..fixture.source_ids.len() {
                for row in 0..2 {
                    assert_eq!(
                        aliased.final_columns[2 * source + row],
                        direct_d3(&fixture, source, row),
                        "source {source} row {row}: the difference-form D3 fold must equal an independent direct multilinear sum",
                    );
                }
            }
        }
        if tail_rounds == 6 {
            assert_eq!(
                aliased.rounds[0].evaluation_rows, 32,
                "the maximum ruled tail must hit the complete 32-row tile boundary",
            );
            assert_eq!(aliased.rounds[1].evaluation_rows, 16);
        }
    }
}

#[test]
fn cpu_main_tail_reference_covers_1012_canonical_sources() {
    let fixture = Fixture::new(maximum_source_program(), 1);
    assert_eq!(fixture.source_ids.len(), 1_012);
    let output = main_tail_reference(fixture.input(MainTailClaimOutput::Detached)).unwrap();
    assert_eq!(output.rounds.len(), 1);
    assert_eq!(output.rounds[0].evaluation_rows, 1);
    assert_eq!(output.final_stride, 2);
    assert_eq!(output.final_columns.len(), 1_012 * 2);
}

#[test]
fn cpu_main_tail_mutation_conventions_are_live() {
    let fixture = Fixture::new(rich_program(), 5);
    let correct = main_tail_reference(fixture.input(MainTailClaimOutput::Aliased)).unwrap();

    let mut old_point_as_fold_challenges =
        Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    old_point_as_fold_challenges.generated_challenges =
        old_point_as_fold_challenges.claim_coordinates.clone();
    let old_point_result =
        main_tail_reference(old_point_as_fold_challenges.input(MainTailClaimOutput::Aliased))
            .unwrap();
    assert_ne!(
        old_point_result.rounds[0].coefficients,
        correct.rounds[0].coefficients,
        "using the incoming claim point for the D3 entry fold must change the first tail polynomial",
    );
    let mut missing_fold_challenges = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    missing_fold_challenges
        .generated_challenges
        .truncate(usize::from(missing_fold_challenges.entry_round) - 1);
    assert!(matches!(
        main_tail_reference(missing_fold_challenges.input(MainTailClaimOutput::Aliased)),
        Err(MainTailReferenceError::GeneratedChallenges { .. })
    ));

    for (label, mutation) in [
        (
            "reversed D3 challenges",
            MainTailReferenceMutation::ReverseD3Challenges,
        ),
        (
            "permuted monotone q order",
            MainTailReferenceMutation::PermuteD3QOrder,
        ),
        (
            "plain weighted leaves in the difference accumulator",
            MainTailReferenceMutation::WrongD3WeightedForm,
        ),
    ] {
        let mutated = main_tail_reference_with_mutation(
            fixture.input(MainTailClaimOutput::Aliased),
            mutation,
        )
        .unwrap();
        assert_ne!(mutated, correct, "{label} must be observable");
    }

    let mut perturbed_leaf = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    perturbed_leaf.columns[0].add_assign(&E4::ONE);
    assert_ne!(
        main_tail_reference(perturbed_leaf.input(MainTailClaimOutput::Aliased)).unwrap(),
        correct,
        "a live entry leaf perturbation must be observable",
    );

    let mut wrong_source = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    wrong_source.source_ids.swap(0, 1);
    assert!(matches!(
        main_tail_reference(wrong_source.input(MainTailClaimOutput::Aliased)),
        Err(MainTailReferenceError::NonCanonicalSource { column: 0, .. })
    ));

    let mut cumulative_eq = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    let folding_steps = usize::from(cumulative_eq.entry_round) + cumulative_eq.tail_rounds;
    cumulative_eq.eq_boundary.eq_sizes = make_eq_sizes(folding_steps - 1);
    cumulative_eq.eq_boundary.semantic_suffix_offset = 1;
    cumulative_eq.entry_eq_low = direct_eq(&cumulative_eq.claim_coordinates[1..folding_steps]);
    assert!(matches!(
        main_tail_reference(cumulative_eq.input(MainTailClaimOutput::Aliased)),
        Err(MainTailReferenceError::BoundarySuffixOffset { .. })
            | Err(MainTailReferenceError::BoundaryEqSizes { .. })
    ));

    let mut suffix_off_by_one = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    suffix_off_by_one.eq_boundary.semantic_suffix_offset += 1;
    assert!(matches!(
        main_tail_reference(suffix_off_by_one.input(MainTailClaimOutput::Aliased)),
        Err(MainTailReferenceError::BoundarySuffixOffset { .. })
    ));

    assert!(matches!(
        main_tail_reference_with_mutation(
            fixture.input(MainTailClaimOutput::Aliased),
            MainTailReferenceMutation::SkipFirstNonFinalEqFold,
        ),
        Err(MainTailReferenceError::EqEvolutionLength { .. })
    ));
    assert_ne!(
        main_tail_reference_with_mutation(
            fixture.input(MainTailClaimOutput::Aliased),
            MainTailReferenceMutation::ExtraFinalEqFold,
        )
        .unwrap(),
        correct
    );

    let mut coefficient_perturbation = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    for coefficient in
        &mut coefficient_perturbation.coefficient_bank[CoefficientRecipeId::RESERVED as usize..]
    {
        coefficient.add_assign(&E4::ONE);
    }
    assert_ne!(
        main_tail_reference(coefficient_perturbation.input(MainTailClaimOutput::Aliased)).unwrap(),
        correct,
        "a live coefficient-bank perturbation must be observable",
    );

    let mut transcript_perturbation = Fixture::new(fixture.program.clone(), fixture.tail_rounds);
    transcript_perturbation.seed[0] ^= 1;
    assert_ne!(
        main_tail_reference(transcript_perturbation.input(MainTailClaimOutput::Aliased)).unwrap(),
        correct,
        "a transcript seed perturbation must be observable",
    );

    let mut entry_eq_perturbation = Fixture::new(fixture.program, fixture.tail_rounds);
    entry_eq_perturbation.entry_eq_low[0].add_assign(&E4::ONE);
    assert!(matches!(
        main_tail_reference(entry_eq_perturbation.input(MainTailClaimOutput::Aliased)),
        Err(MainTailReferenceError::EntryEqValue { index: 0 })
    ));
}

#[test]
fn cpu_main_tail_descriptor_immediates_use_montgomery_raw() {
    struct ImmediateResolver;

    impl CoeffResolver for ImmediateResolver {
        fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
            lift(13 + 17 * id.0)
        }

        fn source_pair(&self, id: SourceId, row: usize) -> (E4, E4) {
            let endpoint0 = lift(29 + 19 * id.0 + 7 * row as u32);
            let mut endpoint1 = endpoint0;
            endpoint1.add_assign(&lift(5 + id.0));
            (endpoint0, endpoint1)
        }
    }

    let (programs, layers) = compile_corpus_layout("mem_word_only_layout_gkr.json");
    let (program, tail_program, canonical_copy) = (0..layers)
        .filter_map(|layer| {
            let program = programs.continuation_layer(layer).clone();
            let tail_program = super::super::lower_main_tail_program(&program).ok()?;
            if tail_program.immediates.is_empty() {
                return None;
            }
            let mut canonical_copy = program.clone();
            canonical_copy.immediates = tail_program
                .immediates
                .iter()
                .map(|&canonical_as_raw| {
                    BF::from_reduced_raw_repr(canonical_as_raw).as_u32_reduced()
                })
                .collect();
            canonical_copy.coefficients.immediates = canonical_copy.immediates.clone();
            let live = (0..32).any(|row| {
                interpret_continuation_program(&program, row, &ImmediateResolver, 8).unwrap()
                    != interpret_continuation_program(&canonical_copy, row, &ImmediateResolver, 8)
                        .unwrap()
            });
            live.then_some((program, tail_program, canonical_copy))
        })
        .next()
        .expect("the fixed mem-word corpus has a live banked immediate");
    assert!(!tail_program.immediates.is_empty());

    let blob = serialize_main_tail_program_blob(&tail_program);
    let packed = tail_program
        .immediates
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let offset = super::super::MAIN_TAIL_IMMEDIATE_OFFSET + index * size_of::<u32>();
            u32::from_le_bytes(blob[offset..offset + size_of::<u32>()].try_into().unwrap())
        })
        .collect::<Vec<_>>();
    let expected = tail_program
        .immediates
        .iter()
        .map(|&canonical| BF::from_u32_with_reduction(canonical).as_u32_raw_repr_reduced())
        .collect::<Vec<_>>();
    assert_eq!(packed, expected);
    assert!(tail_program
        .immediates
        .iter()
        .zip(&packed)
        .any(|(&canonical, &raw)| canonical != raw));

    assert!((0..32).any(|row| {
        interpret_continuation_program(&program, row, &ImmediateResolver, 8).unwrap()
            != interpret_continuation_program(&canonical_copy, row, &ImmediateResolver, 8).unwrap()
    }));
}

#[test]
fn cpu_main_tail_final_publication_preflight_rejects_before_launch() {
    let final_elems = 2_024;
    assert!(matches!(
        validate_main_tail_final_publication_capacity(final_elems, final_elems - 1),
        Err(MainTailBindError::FinalAllocationLength {
            required,
            available,
        }) if required == final_elems && available == final_elems - 1
    ));
    assert!(validate_main_tail_final_publication_capacity(final_elems, final_elems).is_ok());
}

#[test]
fn cpu_main_tail_descriptor_abi_and_blob_sections_are_exact() {
    assert_eq!(size_of::<MainTailDesc>(), 128);
    assert_eq!(align_of::<MainTailDesc>(), 16);
    for (field, actual, expected) in [
        ("program_blob", offset_of!(MainTailDesc, program_blob), 0),
        ("entry", offset_of!(MainTailDesc, entry), 8),
        ("ping", offset_of!(MainTailDesc, ping), 16),
        ("pong", offset_of!(MainTailDesc, pong), 24),
        ("eq_low", offset_of!(MainTailDesc, eq_low), 32),
        (
            "prev_claim_coordinates",
            offset_of!(MainTailDesc, prev_claim_coordinates),
            40,
        ),
        ("seed", offset_of!(MainTailDesc, seed), 48),
        ("claim", offset_of!(MainTailDesc, claim), 56),
        ("eq_prefactor", offset_of!(MainTailDesc, eq_prefactor), 64),
        (
            "coefficients_out",
            offset_of!(MainTailDesc, coefficients_out),
            72,
        ),
        (
            "challenges_out",
            offset_of!(MainTailDesc, challenges_out),
            80,
        ),
        ("eq_sizes", offset_of!(MainTailDesc, eq_sizes), 88),
        (
            "entry_column_elems",
            offset_of!(MainTailDesc, entry_column_elems),
            100,
        ),
        ("source_count", offset_of!(MainTailDesc, source_count), 104),
        (
            "program_words",
            offset_of!(MainTailDesc, program_words),
            106,
        ),
        (
            "immediate_count",
            offset_of!(MainTailDesc, immediate_count),
            108,
        ),
        (
            "c_init_coeff_id",
            offset_of!(MainTailDesc, c_init_coeff_id),
            110,
        ),
        ("tail_start", offset_of!(MainTailDesc, tail_start), 112),
        (
            "folding_steps",
            offset_of!(MainTailDesc, folding_steps),
            113,
        ),
        ("k", offset_of!(MainTailDesc, k), 114),
        ("reserved", offset_of!(MainTailDesc, reserved), 115),
        ("blob_bytes", offset_of!(MainTailDesc, blob_bytes), 116),
        ("tail_padding", offset_of!(MainTailDesc, tail_padding), 120),
    ] {
        assert_eq!(actual, expected, "{field}");
    }
    assert_eq!(MAIN_TAIL_DESCRIPTOR_BYTES, 128);
    assert_eq!(size_of::<MainTailProgramBlob>(), 15_024);
    assert_eq!(align_of::<MainTailProgramBlob>(), 16);
    assert_eq!(MAIN_TAIL_KERNEL_ARGUMENT_BYTES, 15_152);
    assert_eq!(MAIN_TAIL_PARAMETER_HEADROOM, 17_612);

    let program = super::super::lower_main_tail_program(&rich_program()).unwrap();
    let blob = serialize_main_tail_program_blob(&program);
    assert_eq!(blob.len(), super::super::MAIN_TAIL_BLOB_BYTES);
    assert!(
        blob[super::super::MAIN_TAIL_PROGRAM_OFFSET + program.program_words.len() * 2
            ..super::super::MAIN_TAIL_IMMEDIATE_OFFSET]
            .iter()
            .all(|&byte| byte == 0)
    );
    assert!(
        blob[super::super::MAIN_TAIL_IMMEDIATE_OFFSET + program.immediates.len() * 4..]
            .iter()
            .all(|&byte| byte == 0)
    );

    let cuda = include_str!("../../../../native/gkr/backward/main_tail.cuh");
    for assertion in [
        "sizeof(bwd_main_tail_desc) == 128",
        "alignof(bwd_main_tail_desc) == 16",
        "__builtin_offsetof(bwd_main_tail_desc, eq_sizes) == 88",
        "__builtin_offsetof(bwd_main_tail_desc, entry_column_elems) == 100",
        "__builtin_offsetof(bwd_main_tail_desc, source_count) == 104",
        "__builtin_offsetof(bwd_main_tail_desc, tail_start) == 112",
        "__builtin_offsetof(bwd_main_tail_desc, blob_bytes) == 116",
        "sizeof(bwd_main_tail_desc) + sizeof(bwd_main_tail_program_blob) == 15152",
        "BWD_MAIN_TAIL_PARAMETER_CEILING - sizeof(bwd_main_tail_desc) - sizeof(bwd_main_tail_program_blob) == 17612",
    ] {
        assert!(
            cuda.contains(assertion),
            "missing CUDA assertion {assertion}"
        );
    }
}
