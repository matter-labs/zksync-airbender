//! The portable reference backend: works for every `<F, E>` pair on every
//! architecture, with scalar per-relation forward ops and the scalar fused
//! chunk kernel on the backward path. Its pass-wide buffer carries plainly
//! typed `[E; 2]` tri rows — no vector-compatible type-erased slots.

use std::collections::BTreeMap;

use super::super::dimension_reduction::forward::DimensionReducingInputOutput;
use super::super::{GKRStorage, SumcheckIntermediateProofValues};
use super::{DimReducingSumcheckScratch, GKRBackend};
use crate::gkr::prover::EvaluationPointEntry;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};
use transcript::Transcript;
use worker::Worker;

/// The reference backend: scalar execution of the historical algorithms,
/// honoring the caller's schedule (windowed head passes run through the
/// scalar kernel). Transcript-identical to every other backend.
#[derive(Clone, Copy, Debug, Default)]
pub struct NaiveGKRBackend;

impl<F: PrimeField, E: FieldExtension<F> + Field> GKRBackend<F, E> for NaiveGKRBackend
where
    [(); E::DEGREE]: Sized,
{
    type DimensionReducingBuffer = DimReducingSumcheckScratch<E, [E; 2]>;

    fn make_dim_reducing_work_buffers(
        &self,
        max_rounds: usize,
        max_polys: usize,
        worker: &Worker,
    ) -> Self::DimensionReducingBuffer {
        DimReducingSumcheckScratch::new(max_rounds, max_polys, worker)
    }

    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<F, E>,
        compiled_circuit: &GKRCircuitArtifact<F>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        worker: &Worker,
    ) -> (
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    ) {
        super::super::dimension_reduction::forward::evaluate_dimension_reduction_forward_with(
            storage,
            compiled_circuit,
            initial_trace_log_2,
            final_trace_log_2,
            worker,
            super::super::dimension_reduction::forward::forward_pairwise_specialized,
            super::super::dimension_reduction::forward::forward_logup_specialized,
        )
    }

    fn dimension_reducing_sumcheck_for_layer<TR: Transcript<F, E>>(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        layer_idx: usize,
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<E>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<super::super::GKRAddress, E>>,
        gkr_storage: &mut GKRStorage<F, E>,
        batching_challenge: &mut E,
        seed: &mut TR::Seed,
        trace_len_after_reduction: usize,
        worker: &Worker,
        buffers: &mut Self::DimensionReducingBuffer,
    ) -> SumcheckIntermediateProofValues<F, E>
    where
        [(); E::DEGREE]: Sized,
    {
        super::super::sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer_lsb::<
            F,
            E,
            TR,
            [E; 2],
            _,
            _,
        >(
            |inputs, outputs, rels, tp, cs, cl, sp| unsafe {
                super::super::dimension_reduction::lsb_backward::scalar_initial_chunk::<E>(
                    inputs, outputs, rels, tp, cs, cl, sp,
                )
            },
            |buffers, rels, r, tp, cs, cl, sp| unsafe {
                super::super::dimension_reduction::lsb_backward::scalar_continuing_chunk::<E>(
                    buffers, rels, r, tp, cs, cl, sp,
                )
            },
            schedule,
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            seed,
            trace_len_after_reduction,
            worker,
            buffers,
        )
    }

    type NaiveSameSizeFoldBuffer = Box<[core::mem::MaybeUninit<E>]>;
    type WindowedSameSizeFoldBuffer = Box<[core::mem::MaybeUninit<E>]>;
    type UniskipSameSizeFoldBuffer = Box<[core::mem::MaybeUninit<E>]>;

    fn make_naive_same_size_fold_buffers(
        &self,
        _schedule: &[crate::gkr::prover_config::SumcheckStep],
        _trace_len: usize,
        _num_base_polys: usize,
        _num_ext_polys: usize,
    ) -> Vec<Self::NaiveSameSizeFoldBuffer> {
        // the naive loop's lazy folds live inside GKRStorage
        Vec::new()
    }

    fn make_windowed_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::WindowedSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        (0..num_base_polys + num_ext_polys)
            .map(|_| Box::new_uninit_slice(capacity))
            .collect()
    }

    fn make_uniskip_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::UniskipSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        (0..num_base_polys + num_ext_polys)
            .map(|_| Box::new_uninit_slice(capacity))
            .collect()
    }

    type SameSizeChain =
        crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::GenericSameSizeChain<F, E>;

    fn make_same_size_chain(
        &self,
        prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<F, E>,
    ) -> Self::SameSizeChain
    where
        F: field::TwoAdicField,
    {
        crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::GenericSameSizeChain::new(prog)
    }

    fn evaluate_same_size_sumcheck_for_layer<TR: Transcript<F, E>>(
        &self,
        layer_idx: usize,
        layer: &cs::gkr_compiler::GKRLayerDescription<F>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<E>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<super::super::GKRAddress, E>>,
        gkr_storage: &mut GKRStorage<F, E>,
        batching_challenge: &mut E,
        trace_len: usize,
        lookup_challenges_multiplicative_part: E,
        lookup_challenges_additive_part: E,
        inits_and_teardowns_top_bits: &[u32],
        address_high_bits_shift: u32,
        external_challenges: &super::super::GKRExternalChallenges<F, E>,
        prover_config: &crate::gkr::prover_config::ProverConfig,
        seed: &mut TR::Seed,
        worker: &Worker,
    ) -> SumcheckIntermediateProofValues<F, E>
    where
        F: field::TwoAdicField,
        [(); E::DEGREE]: Sized,
    {
        super::super::sumcheck_loop::evaluate_sumcheck_for_layer::<F, E, TR, _>(
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            trace_len,
            lookup_challenges_multiplicative_part,
            lookup_challenges_additive_part,
            inits_and_teardowns_top_bits,
            address_high_bits_shift,
            external_challenges,
            prover_config,
            seed,
            worker,
            |s, t, b, e| self.make_uniskip_same_size_fold_buffers(s, t, b, e),
            |s, t, b, e| self.make_windowed_same_size_fold_buffers(s, t, b, e),
            |prog| self.make_same_size_chain(prog),
        )
    }
}
