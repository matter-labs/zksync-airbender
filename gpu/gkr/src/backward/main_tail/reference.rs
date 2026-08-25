//! Independent scalar oracle for the complete main-layer tail.
//!
//! The oracle consumes the canonical column-major continuation publication,
//! not a kernel descriptor. It folds the D3 seam first, evaluates the retained
//! continuation program with eight logical lists, then performs ordinary D1
//! folds until the dense source stride is two.

use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{
    interpret_continuation_program, CoeffResolver, CoefficientRecipeId, ContinuationLayerProgram,
    LeanInterpError, SourceId,
};

use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::main_tail::{
    lower_main_tail_program, MainTailProgram, MainTailProgramError, MAIN_TAIL_K,
};
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::upstream::{
    commit_field_els, draw_random_field_els, evaluate_eq_poly, evaluate_small_univariate_poly,
    output_univariate_monomial_form_max_quadratic, BabyBearField, Blake2sTranscript, Field, Seed,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MainTailClaimOutput {
    Aliased,
    Detached,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainTailReferenceEntry<'a> {
    pub(crate) source_ids: &'a [SourceId],
    pub(crate) columns: &'a [E4],
    pub(crate) stride: usize,
    pub(crate) depth: u8,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainTailReferenceInput<'a> {
    pub(crate) program: &'a ContinuationLayerProgram,
    pub(crate) tail_program: &'a MainTailProgram,
    pub(crate) coefficient_bank: &'a [E4],
    pub(crate) entry: MainTailReferenceEntry<'a>,
    /// Sumcheck challenges already produced before `entry_round`.
    /// The D3 entry fold consumes the immediately preceding three values.
    pub(crate) generated_challenges: &'a [E4],
    /// The incoming claim point used to normalize each tail round.
    pub(crate) claim_coordinates: &'a [E4],
    pub(crate) entry_eq_low: &'a [E4],
    pub(crate) seed: [u32; 8],
    pub(crate) claim: E4,
    pub(crate) eq_prefactor: E4,
    pub(crate) entry_round: u8,
    pub(crate) eq_boundary: MainEqBoundaryWitness,
    pub(crate) claim_output: MainTailClaimOutput,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MainTailReferenceRound {
    pub(crate) absolute_round: u8,
    pub(crate) semantic_suffix_offset: u8,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) evaluation_rows: usize,
    pub(crate) coefficients: [E4; 4],
    pub(crate) challenge: E4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MainTailReferenceOutput {
    pub(crate) rounds: Vec<MainTailReferenceRound>,
    pub(crate) seed: [u32; 8],
    pub(crate) claim: E4,
    pub(crate) eq_prefactor: E4,
    pub(crate) claim_coordinates: Vec<E4>,
    pub(crate) final_eq_low: Vec<E4>,
    pub(crate) final_eq_sizes: GkrEqSizes,
    pub(crate) final_semantic_suffix_offset: u8,
    pub(crate) final_columns: Vec<E4>,
    pub(crate) final_stride: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MainTailReferenceError {
    TailProgramLowering(MainTailProgramError),
    TailProgramMismatch,
    SourceIdCount {
        expected: usize,
        actual: usize,
    },
    NonCanonicalSource {
        column: usize,
        source: SourceId,
    },
    EntryColumnCount {
        expected: usize,
        actual: usize,
    },
    EntryStride {
        stride: usize,
    },
    EntryDepth {
        expected: u8,
        actual: u8,
    },
    TailRoundCount {
        rounds: usize,
    },
    ClaimCoordinates {
        required: usize,
        actual: usize,
    },
    GeneratedChallenges {
        required: usize,
        actual: usize,
    },
    CoefficientBank {
        required: usize,
        actual: usize,
    },
    BoundaryConsumerRound {
        expected: u8,
        actual: u8,
    },
    BoundarySuffixOffset {
        expected: u8,
        actual: u8,
    },
    BoundaryEqSizes {
        expected: GkrEqSizes,
        actual: GkrEqSizes,
    },
    EntryEqLength {
        expected: usize,
        actual: usize,
    },
    EntryEqValue {
        index: usize,
    },
    EqEvolutionLength {
        round: u8,
        expected: usize,
        actual: usize,
    },
    ZeroEqPrefactor {
        round: u8,
    },
    Interpreter(LeanInterpError),
    FinalStride {
        actual: usize,
    },
}

impl core::fmt::Display for MainTailReferenceError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for MainTailReferenceError {}

impl From<MainTailProgramError> for MainTailReferenceError {
    fn from(error: MainTailProgramError) -> Self {
        Self::TailProgramLowering(error)
    }
}

impl From<LeanInterpError> for MainTailReferenceError {
    fn from(error: LeanInterpError) -> Self {
        Self::Interpreter(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReferenceMutation {
    None,
    ReverseD3Challenges,
    PermuteD3QOrder,
    WrongD3WeightedForm,
    SkipFirstNonFinalEqFold,
    ExtraFinalEqFold,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MainTailReferenceMutation {
    ReverseD3Challenges,
    PermuteD3QOrder,
    WrongD3WeightedForm,
    SkipFirstNonFinalEqFold,
    ExtraFinalEqFold,
}

#[cfg(test)]
impl From<MainTailReferenceMutation> for ReferenceMutation {
    fn from(mutation: MainTailReferenceMutation) -> Self {
        match mutation {
            MainTailReferenceMutation::ReverseD3Challenges => Self::ReverseD3Challenges,
            MainTailReferenceMutation::PermuteD3QOrder => Self::PermuteD3QOrder,
            MainTailReferenceMutation::WrongD3WeightedForm => Self::WrongD3WeightedForm,
            MainTailReferenceMutation::SkipFirstNonFinalEqFold => Self::SkipFirstNonFinalEqFold,
            MainTailReferenceMutation::ExtraFinalEqFold => Self::ExtraFinalEqFold,
        }
    }
}

struct TailResolver<'a> {
    coefficient_bank: &'a [E4],
    columns: &'a [E4],
    stride: usize,
}

impl CoeffResolver for TailResolver<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        self.coefficient_bank[id.0 as usize]
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (E4, E4) {
        let first = self.columns[id.0 as usize * self.stride + 2 * row];
        let second = self.columns[id.0 as usize * self.stride + 2 * row + 1];
        let mut delta = second;
        delta.sub_assign(&first);
        (first, delta)
    }
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

fn semantic_eq(point: &[E4]) -> Vec<E4> {
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

fn reverse_three_bits(value: usize) -> usize {
    ((value & 1) << 2) | (value & 2) | ((value & 4) >> 2)
}

fn fold_d3(
    columns: &[E4],
    source_count: usize,
    stride: usize,
    coordinates: [E4; 3],
    mutation: ReferenceMutation,
) -> Vec<E4> {
    let coordinates = if mutation == ReferenceMutation::ReverseD3Challenges {
        [coordinates[2], coordinates[1], coordinates[0]]
    } else {
        coordinates
    };
    let output_stride = stride >> 3;
    let mut output = vec![E4::ZERO; source_count * output_stride];
    for source in 0..source_count {
        for row in 0..output_stride {
            let input = source * stride + 8 * row;
            let leaf_zero = columns[input];
            let mut folded = leaf_zero;
            for q in 1..8 {
                let mut weight = E4::ONE;
                for (bit, coordinate) in coordinates.iter().enumerate() {
                    weight.mul_assign(&eq_weight((q >> bit) & 1, *coordinate));
                }
                let leaf = if mutation == ReferenceMutation::PermuteD3QOrder {
                    columns[input + reverse_three_bits(q)]
                } else {
                    columns[input + q]
                };
                if mutation == ReferenceMutation::WrongD3WeightedForm {
                    let mut contribution = leaf;
                    contribution.mul_assign(&weight);
                    folded.add_assign(&contribution);
                } else {
                    let mut difference = leaf;
                    difference.sub_assign(&leaf_zero);
                    difference.mul_assign(&weight);
                    folded.add_assign(&difference);
                }
            }
            output[source * output_stride + row] = folded;
        }
    }
    output
}

fn fold_d1(columns: &[E4], source_count: usize, stride: usize, challenge: E4) -> Vec<E4> {
    let output_stride = stride >> 1;
    let mut output = vec![E4::ZERO; source_count * output_stride];
    for source in 0..source_count {
        for row in 0..output_stride {
            let first = columns[source * stride + 2 * row];
            let mut delta = columns[source * stride + 2 * row + 1];
            delta.sub_assign(&first);
            delta.mul_assign(&challenge);
            delta.add_assign(&first);
            output[source * output_stride + row] = delta;
        }
    }
    output
}

fn fold_eq(eq: &[E4]) -> Vec<E4> {
    eq.chunks_exact(2)
        .map(|pair| {
            let mut folded = pair[0];
            folded.add_assign(&pair[1]);
            folded
        })
        .collect()
}

fn round_update(
    e_partial: E4,
    c_partial: E4,
    previous_coordinate: E4,
    seed: &mut Seed,
    claim: &mut E4,
    eq_prefactor: &mut E4,
    absolute_round: u8,
) -> Result<([E4; 4], E4), MainTailReferenceError> {
    let inverse = eq_prefactor
        .inverse()
        .ok_or(MainTailReferenceError::ZeroEqPrefactor {
            round: absolute_round,
        })?;
    let mut normalized_claim = *claim;
    normalized_claim.mul_assign(&inverse);
    let coefficients = output_univariate_monomial_form_max_quadratic::<BabyBearField, E4>(
        previous_coordinate,
        normalized_claim,
        e_partial,
        c_partial,
    );
    commit_field_els::<BabyBearField, E4, Blake2sTranscript>(seed, &coefficients);
    let challenge = draw_random_field_els::<BabyBearField, E4, Blake2sTranscript>(seed, 1)[0];
    *claim = evaluate_small_univariate_poly::<BabyBearField, E4, 4>(&coefficients, &challenge);
    *eq_prefactor = evaluate_eq_poly::<BabyBearField, E4>(&challenge, &previous_coordinate);
    Ok((coefficients, challenge))
}

fn main_tail_reference_inner(
    input: MainTailReferenceInput<'_>,
    mutation: ReferenceMutation,
) -> Result<MainTailReferenceOutput, MainTailReferenceError> {
    let expected_tail_program = lower_main_tail_program(input.program)?;
    if expected_tail_program != *input.tail_program
        || usize::from(input.tail_program.k) != MAIN_TAIL_K
    {
        return Err(MainTailReferenceError::TailProgramMismatch);
    }

    let source_count = input.program.coefficients.sources.len();
    if input.entry.source_ids.len() != source_count {
        return Err(MainTailReferenceError::SourceIdCount {
            expected: source_count,
            actual: input.entry.source_ids.len(),
        });
    }
    for (column, source) in input.entry.source_ids.iter().copied().enumerate() {
        if source != SourceId(column as u32) {
            return Err(MainTailReferenceError::NonCanonicalSource { column, source });
        }
    }
    if input.entry.stride < 16 || !input.entry.stride.is_power_of_two() {
        return Err(MainTailReferenceError::EntryStride {
            stride: input.entry.stride,
        });
    }
    let expected_column_count = source_count.checked_mul(input.entry.stride).ok_or(
        MainTailReferenceError::EntryStride {
            stride: input.entry.stride,
        },
    )?;
    if input.entry.columns.len() != expected_column_count {
        return Err(MainTailReferenceError::EntryColumnCount {
            expected: expected_column_count,
            actual: input.entry.columns.len(),
        });
    }

    let expected_entry_depth =
        input
            .entry_round
            .checked_sub(3)
            .ok_or(MainTailReferenceError::EntryDepth {
                expected: 0,
                actual: input.entry.depth,
            })?;
    if input.entry.depth != expected_entry_depth {
        return Err(MainTailReferenceError::EntryDepth {
            expected: expected_entry_depth,
            actual: input.entry.depth,
        });
    }
    let stride_bits = input.entry.stride.ilog2() as usize;
    let folding_steps = usize::from(input.entry.depth)
        .checked_add(stride_bits)
        .ok_or(MainTailReferenceError::EntryStride {
            stride: input.entry.stride,
        })?;
    let tail_rounds = folding_steps
        .checked_sub(usize::from(input.entry_round))
        .ok_or(MainTailReferenceError::TailRoundCount { rounds: 0 })?;
    if !(1..=6).contains(&tail_rounds) {
        return Err(MainTailReferenceError::TailRoundCount {
            rounds: tail_rounds,
        });
    }
    if input.claim_coordinates.len() < folding_steps {
        return Err(MainTailReferenceError::ClaimCoordinates {
            required: folding_steps,
            actual: input.claim_coordinates.len(),
        });
    }
    if input.generated_challenges.len() < usize::from(input.entry_round) {
        return Err(MainTailReferenceError::GeneratedChallenges {
            required: usize::from(input.entry_round),
            actual: input.generated_challenges.len(),
        });
    }
    let coefficient_count = usize::from(input.tail_program.coefficient_count);
    if input.coefficient_bank.len() < coefficient_count {
        return Err(MainTailReferenceError::CoefficientBank {
            required: coefficient_count,
            actual: input.coefficient_bank.len(),
        });
    }

    if input.eq_boundary.consumer_round != input.entry_round {
        return Err(MainTailReferenceError::BoundaryConsumerRound {
            expected: input.entry_round,
            actual: input.eq_boundary.consumer_round,
        });
    }
    let expected_suffix_offset = input.entry_round + 1;
    if input.eq_boundary.semantic_suffix_offset != expected_suffix_offset {
        return Err(MainTailReferenceError::BoundarySuffixOffset {
            expected: expected_suffix_offset,
            actual: input.eq_boundary.semantic_suffix_offset,
        });
    }
    let expected_entry_sizes = make_eq_sizes(tail_rounds - 1);
    if input.eq_boundary.eq_sizes != expected_entry_sizes {
        return Err(MainTailReferenceError::BoundaryEqSizes {
            expected: expected_entry_sizes,
            actual: input.eq_boundary.eq_sizes,
        });
    }

    let semantic_eq =
        semantic_eq(&input.claim_coordinates[usize::from(expected_suffix_offset)..folding_steps]);
    if input.entry_eq_low.len() != semantic_eq.len() {
        return Err(MainTailReferenceError::EntryEqLength {
            expected: semantic_eq.len(),
            actual: input.entry_eq_low.len(),
        });
    }
    if let Some(index) = input
        .entry_eq_low
        .iter()
        .zip(&semantic_eq)
        .position(|(actual, expected)| actual != expected)
    {
        return Err(MainTailReferenceError::EntryEqValue { index });
    }

    let d3_coordinates: [E4; 3] = input.generated_challenges
        [usize::from(input.entry_round) - 3..usize::from(input.entry_round)]
        .try_into()
        .expect("the entry round was checked to have three preceding challenges");
    let mut columns = fold_d3(
        input.entry.columns,
        source_count,
        input.entry.stride,
        d3_coordinates,
        mutation,
    );
    let mut stride = input.entry.stride >> 3;
    let mut eq_low = input.entry_eq_low.to_vec();
    let mut eq_sizes = input.eq_boundary.eq_sizes;
    let mut semantic_suffix_offset = input.eq_boundary.semantic_suffix_offset;
    let mut claim_coordinates = input.claim_coordinates.to_vec();
    let mut transcript_seed = Seed(input.seed);
    let mut claim = input.claim;
    let mut eq_prefactor = input.eq_prefactor;
    let mut rounds = Vec::with_capacity(tail_rounds);

    for iteration in 0..tail_rounds {
        let absolute_round = input.entry_round + iteration as u8;
        let expected_suffix_offset = absolute_round + 1;
        let expected_eq_sizes = make_eq_sizes(folding_steps - usize::from(absolute_round) - 1);
        debug_assert_eq!(semantic_suffix_offset, expected_suffix_offset);
        debug_assert_eq!(eq_sizes, expected_eq_sizes);
        let evaluation_rows = stride >> 1;
        if eq_low.len() != evaluation_rows {
            return Err(MainTailReferenceError::EqEvolutionLength {
                round: absolute_round,
                expected: evaluation_rows,
                actual: eq_low.len(),
            });
        }

        let resolver = TailResolver {
            coefficient_bank: input.coefficient_bank,
            columns: &columns,
            stride,
        };
        let mut e_partial = E4::ZERO;
        let mut c_partial = E4::ZERO;
        for (row, eq_weight) in eq_low.iter().copied().enumerate() {
            let (mut e, mut c) =
                interpret_continuation_program(input.program, row, &resolver, MAIN_TAIL_K)?;
            e.mul_assign(&eq_weight);
            c.mul_assign(&eq_weight);
            e_partial.add_assign(&e);
            c_partial.add_assign(&c);
        }

        // Read before a potentially aliasing challenge store, matching the
        // device-side contract for the main-layer claim-point symbol.
        let previous_coordinate = claim_coordinates[usize::from(absolute_round)];
        let (coefficients, challenge) = round_update(
            e_partial,
            c_partial,
            previous_coordinate,
            &mut transcript_seed,
            &mut claim,
            &mut eq_prefactor,
            absolute_round,
        )?;
        if input.claim_output == MainTailClaimOutput::Aliased {
            claim_coordinates[usize::from(absolute_round)] = challenge;
        }
        rounds.push(MainTailReferenceRound {
            absolute_round,
            semantic_suffix_offset,
            eq_sizes,
            evaluation_rows,
            coefficients,
            challenge,
        });

        if iteration + 1 < tail_rounds {
            columns = fold_d1(&columns, source_count, stride, challenge);
            stride >>= 1;
            if !(mutation == ReferenceMutation::SkipFirstNonFinalEqFold && iteration == 0) {
                eq_low = fold_eq(&eq_low);
            }
            semantic_suffix_offset += 1;
            eq_sizes = make_eq_sizes(folding_steps - usize::from(absolute_round) - 2);
        } else if mutation == ReferenceMutation::ExtraFinalEqFold {
            eq_low = fold_eq(&eq_low);
        }
    }

    if stride != 2 {
        return Err(MainTailReferenceError::FinalStride { actual: stride });
    }
    Ok(MainTailReferenceOutput {
        rounds,
        seed: transcript_seed.0,
        claim,
        eq_prefactor,
        claim_coordinates,
        final_eq_low: eq_low,
        final_eq_sizes: eq_sizes,
        final_semantic_suffix_offset: semantic_suffix_offset,
        final_columns: columns,
        final_stride: stride,
    })
}

pub(crate) fn main_tail_reference(
    input: MainTailReferenceInput<'_>,
) -> Result<MainTailReferenceOutput, MainTailReferenceError> {
    main_tail_reference_inner(input, ReferenceMutation::None)
}

#[cfg(test)]
pub(crate) fn main_tail_reference_with_mutation(
    input: MainTailReferenceInput<'_>,
    mutation: MainTailReferenceMutation,
) -> Result<MainTailReferenceOutput, MainTailReferenceError> {
    main_tail_reference_inner(input, mutation.into())
}
