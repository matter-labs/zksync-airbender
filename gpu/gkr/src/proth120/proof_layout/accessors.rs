use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::Range;

use crate::upstream::{
    Field, GKRExternalChallenges, OutputType, SumcheckIntermediateProofValues,
    SumcheckRoundCoefficients, PR,
};

use super::ProofLayoutPr;

#[derive(Clone, Debug)]
pub struct GkrProofFields {
    pub external_challenges: GKRExternalChallenges<PR, PR>,
    pub lookup_challenges_pow_nonce: u64,
    pub final_explicit_evaluations: BTreeMap<OutputType, [Vec<PR>; 2]>,
    pub sumcheck_intermediate_values: BTreeMap<usize, SumcheckIntermediateProofValues<PR, PR>>,
    pub grand_product_accumulator_computed: PR,
    pub batched_proximity_check_pow_nonce: u64,
    pub merged_claims: (Vec<PR>, Vec<PR>),
    pub evaluation_point: Vec<PR>,
    pub batching_challenge: PR,
    pub intermediate_transcript_seed: [u8; 32],
}

impl ProofLayoutPr {
    pub fn parse_whir_fields<'a>(&self, bytes: &'a [u8]) -> super::WhirProofFieldsPr<'a> {
        self.validate_host_blob(bytes);
        self.whir.parse(bytes)
    }

    fn validate_host_blob(&self, bytes: &[u8]) {
        assert!(
            bytes.len() >= self.bytes_len(),
            "Proth120 proof blob is undersized"
        );
        assert_eq!(
            bytes.as_ptr() as usize % 32,
            0,
            "Proth120 proof blob is misaligned"
        );
    }

    pub(crate) fn host_fields<'a>(&self, bytes: &'a [u8], range: &Range<usize>) -> &'a [PR] {
        self.validate_host_blob(bytes);
        assert!(
            range.end <= self.bytes_len()
                && range.len().is_multiple_of(16)
                && range.start.is_multiple_of(16),
            "Proth120 proof field range is invalid"
        );
        let values = unsafe {
            std::slice::from_raw_parts(
                bytes.as_ptr().add(range.start).cast::<PR>(),
                range.len() / 16,
            )
        };
        assert!(
            values.iter().all(|value| value.0 < PR::ORDER),
            "Proth120 proof field is noncanonical"
        );
        values
    }

    pub fn parse_gkr_fields(&self, bytes: &[u8]) -> GkrProofFields {
        self.validate_host_blob(bytes);
        let fields = |range: &Range<usize>| self.host_fields(bytes, range);
        let nonce = |range: &Range<usize>| {
            u64::from_ne_bytes(
                bytes[range.clone()]
                    .try_into()
                    .expect("Proth120 proof nonce length mismatch"),
            )
        };
        let final_explicit_evaluations: BTreeMap<_, _> = self
            .output_evaluations
            .iter()
            .map(|(kind, ranges)| {
                (
                    *kind,
                    [
                        fields(&ranges.read_set).to_vec(),
                        fields(&ranges.write_set).to_vec(),
                    ],
                )
            })
            .collect();
        let sumcheck_intermediate_values = self
            .backward_layers
            .iter()
            .map(|layer| {
                let coefficients = fields(&layer.internal_round_coefficients);
                assert_eq!(
                    coefficients.len(),
                    layer.sumcheck_num_rounds * 4,
                    "Proth120 proof round count mismatch"
                );
                let finals = fields(&layer.final_step_evaluations);
                let extras = fields(&layer.extra_evaluations);
                let value = SumcheckIntermediateProofValues {
                    sumcheck_num_rounds: layer.sumcheck_num_rounds,
                    internal_round_coefficients: coefficients
                        .as_chunks::<4>()
                        .0
                        .iter()
                        .copied()
                        .map(SumcheckRoundCoefficients::Multilinear)
                        .collect(),
                    final_step_evaluations: layer
                        .final_step_eval_addresses
                        .iter()
                        .enumerate()
                        .map(|(index, address)| {
                            let start = index * layer.final_step_eval_degree;
                            (
                                *address,
                                finals[start..start + layer.final_step_eval_degree].to_vec(),
                            )
                        })
                        .collect(),
                    extra_evaluations_from_caching_relations: layer
                        .extra_evaluations_addresses
                        .iter()
                        .copied()
                        .zip(extras.iter().copied())
                        .collect(),
                    _marker: PhantomData,
                };
                (layer.layer_idx, value)
            })
            .collect();
        let product = |kind: OutputType| {
            final_explicit_evaluations
                .get(&kind)
                .expect("Proth120 proof product output is missing")
                .each_ref()
                .map(|values| {
                    values.iter().fold(PR::ONE, |mut product, value| {
                        product.mul_assign(value);
                        product
                    })
                })
        };
        let [read, write] = product(OutputType::PermutationProduct);
        let mut grand_product_accumulator_computed = write;
        grand_product_accumulator_computed
            .mul_assign(&read.inverse().expect("Proth120 proof read product is zero"));
        if final_explicit_evaluations.contains_key(&OutputType::InitsAndTeardownsProduct) {
            let [init, teardown] = product(OutputType::InitsAndTeardownsProduct);
            grand_product_accumulator_computed.mul_assign(&teardown);
            grand_product_accumulator_computed
                .mul_assign(&init.inverse().expect("Proth120 proof init product is zero"));
        }
        GkrProofFields {
            external_challenges: GKRExternalChallenges::from_slice(
                &fields(&self.external_challenges)
                    [..GKRExternalChallenges::<PR, PR>::TOTAL_CHALLENGES],
            ),
            lookup_challenges_pow_nonce: nonce(&self.lookup_challenges_pow_nonce),
            final_explicit_evaluations,
            sumcheck_intermediate_values,
            grand_product_accumulator_computed,
            batched_proximity_check_pow_nonce: nonce(&self.batched_proximity_check_pow_nonce),
            merged_claims: (
                fields(&self.memory_claims).to_vec(),
                fields(&self.setup_claims).to_vec(),
            ),
            evaluation_point: fields(&self.evaluation_point).to_vec(),
            batching_challenge: fields(&self.batching_challenge)[0],
            intermediate_transcript_seed: bytes[self.intermediate_transcript_seed.clone()]
                .try_into()
                .expect("Proth120 proof seed length mismatch"),
        }
    }
}
