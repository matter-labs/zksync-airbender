use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

use crate::forward::ForwardOutputSlabTarget;
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::{GKRAddress, OutputType, ProverConfig, PR};

mod build_inputs;

#[derive(Clone, Copy)]
pub enum SectionId {
    OutputEvaluations,
    ExternalChallenges,
    LookupPowNonce,
    RoundCoefficients(usize),
    FinalStepEvaluations(usize),
    ExtraEvaluations(usize),
    GrandProductAccumulator,
    MemoryClaims,
    SetupClaims,
    EvaluationPoint,
    BatchingChallenge,
    BatchedPowNonce,
    SeedSnapshot,
}

pub struct BackwardLayerLayoutPr {
    pub layer_idx: usize,
    pub sumcheck_num_rounds: usize,
    pub final_step_eval_degree: usize,
    pub internal_round_coefficients: Range<usize>,
    pub final_step_evaluations: Range<usize>,
    pub final_step_eval_addresses: Vec<GKRAddress>,
    pub extra_evaluations: Range<usize>,
    pub extra_evaluations_addresses: Vec<GKRAddress>,
}

pub struct OutputEvaluationsLayoutPr {
    pub read_set: Range<usize>,
    pub write_set: Range<usize>,
}

pub struct ProofLayoutPr {
    pub output_evaluations: BTreeMap<OutputType, OutputEvaluationsLayoutPr>,
    pub output_evaluations_range: Range<usize>,
    pub backward_layers: Vec<BackwardLayerLayoutPr>,
    pub external_challenges: Range<usize>,
    pub lookup_challenges_pow_nonce: Range<usize>,
    pub grand_product_accumulator_computed: Range<usize>,
    pub memory_claims: Range<usize>,
    pub setup_claims: Range<usize>,
    pub evaluation_point: Range<usize>,
    pub batching_challenge: Range<usize>,
    pub batched_proximity_check_pow_nonce: Range<usize>,
    pub intermediate_transcript_seed: Range<usize>,
    bytes_len: usize,
}

fn section(cursor: &mut usize, bytes: usize) -> Range<usize> {
    let start = cursor
        .checked_add(31)
        .expect("Proth120 proof alignment overflow")
        & !31;
    let end = start
        .checked_add(bytes)
        .expect("Proth120 proof section overflow");
    *cursor = end;
    start..end
}

fn fields(cursor: &mut usize, count: usize) -> Range<usize> {
    section(
        cursor,
        count
            .checked_mul(size_of::<PR>())
            .expect("Proth120 proof field count overflow"),
    )
}

impl ProofLayoutPr {
    pub fn new(programs: &GkrProgramsPr, config: &ProverConfig) -> Self {
        let circuit = &programs.runtime_circuit;
        let log = circuit.trace_len.trailing_zeros() as usize;
        assert_eq!(
            config.trace_len_log2, log,
            "Proth120 proof config trace log mismatch"
        );
        assert_eq!(
            config.sumcheck_explicit_output_size_log_2, 4,
            "Proth120 proof final trace log must be 4"
        );
        let mut cursor = 0;
        let mut output_evaluations = BTreeMap::new();
        for (kind, addresses) in &circuit.global_output_map {
            assert_eq!(
                addresses.len(),
                2,
                "Proth120 proof output arity must be two"
            );
            output_evaluations.insert(
                *kind,
                OutputEvaluationsLayoutPr {
                    read_set: fields(&mut cursor, 16),
                    write_set: fields(&mut cursor, 16),
                },
            );
        }
        let output_evaluations_range = 0..cursor;
        let backward_layers = build_inputs::layers(programs, 4)
            .into_iter()
            .map(|d| BackwardLayerLayoutPr {
                layer_idx: d.layer_idx,
                sumcheck_num_rounds: d.rounds,
                final_step_eval_degree: d.degree,
                internal_round_coefficients: fields(
                    &mut cursor,
                    d.rounds
                        .checked_mul(4)
                        .expect("Proth120 proof round count overflow"),
                ),
                final_step_evaluations: fields(
                    &mut cursor,
                    d.inputs
                        .len()
                        .checked_mul(d.degree)
                        .expect("Proth120 proof final count overflow"),
                ),
                extra_evaluations: fields(&mut cursor, d.extras.len()),
                final_step_eval_addresses: d.inputs,
                extra_evaluations_addresses: d.extras,
            })
            .collect();
        let external_challenges = fields(&mut cursor, 9);
        let lookup_challenges_pow_nonce = section(&mut cursor, 8);
        let grand_product_accumulator_computed = fields(&mut cursor, 1);
        let memory_claim_count =
            (circuit.memory_layout.total_width + circuit.witness_layout.total_width).div_ceil(16);
        let setup_claim_count = circuit.generic_lookup_tables_width.div_ceil(16);
        let claims = fields(
            &mut cursor,
            memory_claim_count
                .checked_add(setup_claim_count)
                .expect("Proth120 proof claim count overflow"),
        );
        let split = claims
            .start
            .checked_add(
                memory_claim_count
                    .checked_mul(16)
                    .expect("Proth120 proof claim bytes overflow"),
            )
            .expect("Proth120 proof claim split overflow");
        let memory_claims = claims.start..split;
        let setup_claims = split..claims.end;
        let evaluation_point = fields(
            &mut cursor,
            log.checked_add(4)
                .expect("Proth120 proof point count overflow"),
        );
        let batching_challenge = fields(&mut cursor, 1);
        let batched_proximity_check_pow_nonce = section(&mut cursor, 8);
        let intermediate_transcript_seed = section(&mut cursor, 32);
        let bytes_len = cursor
            .checked_add(31)
            .expect("Proth120 proof size overflow")
            & !31;
        let result = Self {
            output_evaluations,
            output_evaluations_range,
            backward_layers,
            external_challenges,
            lookup_challenges_pow_nonce,
            grand_product_accumulator_computed,
            memory_claims,
            setup_claims,
            evaluation_point,
            batching_challenge,
            batched_proximity_check_pow_nonce,
            intermediate_transcript_seed,
            bytes_len,
        };
        result.validate_geometry(log, circuit.layers.len());
        result
    }

    pub fn bytes_len(&self) -> usize {
        self.bytes_len
    }

    pub(crate) fn range(&self, section: SectionId) -> &Range<usize> {
        let layer = |index| {
            self.backward_layers
                .iter()
                .find(|layer| layer.layer_idx == index)
                .unwrap_or_else(|| panic!("Proth120 proof layer {index} is missing"))
        };
        match section {
            SectionId::OutputEvaluations => &self.output_evaluations_range,
            SectionId::ExternalChallenges => &self.external_challenges,
            SectionId::LookupPowNonce => &self.lookup_challenges_pow_nonce,
            SectionId::RoundCoefficients(index) => &layer(index).internal_round_coefficients,
            SectionId::FinalStepEvaluations(index) => &layer(index).final_step_evaluations,
            SectionId::ExtraEvaluations(index) => &layer(index).extra_evaluations,
            SectionId::GrandProductAccumulator => &self.grand_product_accumulator_computed,
            SectionId::MemoryClaims => &self.memory_claims,
            SectionId::SetupClaims => &self.setup_claims,
            SectionId::EvaluationPoint => &self.evaluation_point,
            SectionId::BatchingChallenge => &self.batching_challenge,
            SectionId::BatchedPowNonce => &self.batched_proximity_check_pow_nonce,
            SectionId::SeedSnapshot => &self.intermediate_transcript_seed,
        }
    }

    pub(crate) fn validate_geometry(&self, trace_log: usize, main_layers: usize) {
        let mut ranges = vec![self.output_evaluations_range.clone()];
        for layer in &self.backward_layers {
            ranges.extend([
                layer.internal_round_coefficients.clone(),
                layer.final_step_evaluations.clone(),
                layer.extra_evaluations.clone(),
            ]);
        }
        ranges.extend([
            self.external_challenges.clone(),
            self.lookup_challenges_pow_nonce.clone(),
            self.grand_product_accumulator_computed.clone(),
            self.memory_claims.start..self.setup_claims.end,
            self.evaluation_point.clone(),
            self.batching_challenge.clone(),
            self.batched_proximity_check_pow_nonce.clone(),
            self.intermediate_transcript_seed.clone(),
        ]);
        let mut end = 0;
        assert_eq!(
            self.memory_claims.end, self.setup_claims.start,
            "Proth120 proof claim mirrors must be contiguous"
        );
        for range in ranges {
            assert_eq!(
                range.start % 32,
                0,
                "Proth120 proof section alignment mismatch"
            );
            assert!(
                range.start >= end && range.end >= range.start && range.end <= self.bytes_len,
                "Proth120 proof sections overlap or exceed slab"
            );
            end = range.end;
        }
        assert_eq!(
            self.output_evaluations_range.start, 0,
            "Proth120 output evaluations must be the slab prefix"
        );
        assert_eq!(
            self.backward_layers.len(),
            trace_log - 4 + main_layers,
            "Proth120 proof layer count mismatch"
        );
        assert!(
            self.backward_layers
                .iter()
                .enumerate()
                .all(|(slot, layer)| layer.layer_idx == self.backward_layers.len() - slot - 1),
            "Proth120 proof layer indices mismatch"
        );
        assert_eq!(
            self.evaluation_point.len(),
            (trace_log + 4) * 16,
            "Proth120 proof point geometry mismatch"
        );
        if trace_log == 22 && main_layers == 5 {
            assert_eq!(self.backward_layers.len(), 23);
            assert_eq!(self.memory_claims.len(), 7 * 16);
            assert_eq!(self.setup_claims.len(), 16);
            assert_eq!(self.evaluation_point.len(), 26 * 16);
        }
    }
}

pub struct ProofSlabPr {
    pub backing: Arc<DeviceAllocation<PR>>,
    pub layout: Arc<ProofLayoutPr>,
}

impl ProofSlabPr {
    pub fn new(layout: Arc<ProofLayoutPr>, context: &ProverContext) -> CudaResult<Self> {
        let backing =
            Arc::new(context.alloc(layout.bytes_len() / 16, AllocationPlacement::BestFit)?);
        assert_eq!(
            backing.as_ptr() as usize % 32,
            0,
            "Proth120 proof slab alignment mismatch"
        );
        Ok(Self { backing, layout })
    }
    pub fn output_evaluations_target(&self) -> ForwardOutputSlabTarget<PR> {
        assert_eq!(
            self.layout.output_evaluations_range.start, 0,
            "Proth120 output evaluations must be the slab prefix"
        );
        ForwardOutputSlabTarget {
            backing: Arc::clone(&self.backing),
            len: self.layout.output_evaluations_range.len() / 16,
        }
    }
    pub unsafe fn bytes_mut(&self, section: SectionId) -> (*mut u8, usize) {
        let range = self.layout.range(section);
        (
            unsafe { self.backing.as_ptr().cast::<u8>().add(range.start) } as *mut u8,
            range.len(),
        )
    }
    pub(crate) fn fields_device_mut(&mut self, section: SectionId) -> &mut DeviceSlice<PR> {
        let range = self.layout.range(section);
        assert_eq!(
            range.len() % 16,
            0,
            "Proth120 field section length mismatch"
        );
        unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.backing.as_ptr().cast::<u8>().add(range.start) as *mut PR,
                range.len() / 16,
            )
        }
    }
    pub fn output_evaluations_device_mut(&mut self) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::OutputEvaluations)
    }
    pub fn external_challenges_device_mut(&mut self) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::ExternalChallenges)
    }
    pub fn round_coefficients_device_mut(&mut self, layer: usize) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::RoundCoefficients(layer))
    }
    pub fn final_step_evaluations_device_mut(&mut self, layer: usize) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::FinalStepEvaluations(layer))
    }
    pub fn extra_evaluations_device_mut(&mut self, layer: usize) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::ExtraEvaluations(layer))
    }
    pub fn grand_product_accumulator_device_mut(&mut self) -> &mut DeviceVariable<PR> {
        &mut self.fields_device_mut(SectionId::GrandProductAccumulator)[0]
    }
    pub fn memory_claims_device_mut(&mut self) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::MemoryClaims)
    }
    pub fn setup_claims_device_mut(&mut self) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::SetupClaims)
    }
    pub fn evaluation_point_device_mut(&mut self) -> &mut DeviceSlice<PR> {
        self.fields_device_mut(SectionId::EvaluationPoint)
    }
    pub fn batching_challenge_device_mut(&mut self) -> &mut DeviceVariable<PR> {
        &mut self.fields_device_mut(SectionId::BatchingChallenge)[0]
    }
    pub fn lookup_nonce_device_mut(&mut self) -> &mut DeviceVariable<u64> {
        let (pointer, _) = unsafe { self.bytes_mut(SectionId::LookupPowNonce) };
        unsafe { DeviceVariable::from_raw_parts_mut(pointer.cast()) }
    }
    pub fn batched_nonce_device_mut(&mut self) -> &mut DeviceVariable<u64> {
        let (pointer, _) = unsafe { self.bytes_mut(SectionId::BatchedPowNonce) };
        unsafe { DeviceVariable::from_raw_parts_mut(pointer.cast()) }
    }
    pub fn seed_snapshot_device_mut(&mut self) -> &mut DeviceSlice<u8> {
        let (pointer, len) = unsafe { self.bytes_mut(SectionId::SeedSnapshot) };
        unsafe { DeviceSlice::from_raw_parts_mut(pointer, len) }
    }
}
