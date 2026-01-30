use std::alloc::Global;
use std::mem::MaybeUninit;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::TwoAdicField;
use field::{Field, FieldExtension, PrimeField};
use worker::WorkerGeometry;

use super::*;
use crate::fft::Twiddles;
use crate::gkr::prover::setup::GKRSetupPrecomputations;
use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::merkle_trees::ColumnMajorMerkleTreeConstructor;
use crate::merkle_trees::MerkleTreeCapVarLength;
use crate::worker::Worker;

use cs::definitions::NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES;

pub mod forward_loop;
pub mod setup;
pub mod stages;

#[derive(Clone, Debug)]
pub struct BaseFieldCosetBoundTracePart<F: PrimeField + TwoAdicField> {
    pub columns: Vec<Box<[F]>>,
    pub offset: F,
}

#[derive(
    Clone, Copy, Debug, Hash, Default, serde::Serialize, serde::Deserialize, PartialEq, Eq,
)]
#[repr(C)]
pub struct GKRExternalChallenges<F: PrimeField, E: FieldExtension<F> + Field> {
    pub permutation_argument_linearization_challenges:
        [E; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    pub permutation_argument_additive_part: E,
    pub _marker: core::marker::PhantomData<F>,
}

pub struct GKRProverData<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub external_challenges: GKRExternalChallenges<F, E>,
    // pub stage_1_result: FirstStageOutput<N, A, T>,
    // pub stage_2_result: SecondStageOutput<N, A, T>,
    // pub quotient_commitment_result: ThirdStageOutput<N, A, T>,
    // pub deep_poly_result: FourthStageOutput<N, A, T>,
    // pub fri_result: FifthStageOutput<A, T>,
    _marker: core::marker::PhantomData<T>,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct GKRProof<F: PrimeField, E: FieldExtension<F> + Field> {
    pub external_challenges: GKRExternalChallenges<F, E>,
    pub witness_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub memory_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub setup_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub permutation_grand_product_accumulator: E,
    pub evaluations_at_random_points: Vec<E>,

    // TODO: WHIR intermediate oracles
    pub proximity_check_inteermediate_oracles: Vec<MerkleTreeCapVarLength>,
    pub last_proximity_check_step_plain_leaf_values: Vec<Vec<E>>,
    pub final_monomial_form: Vec<E>,
    // TODO: queries
    // pub queries: Vec<QuerySet>,
    pub pow_nonce: u64,
}

pub(crate) fn split_destinations<T: Sized>(
    dest: Vec<&'_ mut [T]>,
    geometry: WorkerGeometry,
) -> Vec<Vec<&'_ mut [T]>> {
    let len = dest.len();
    let mut result = Vec::with_capacity(geometry.len());
    for _ in 0..geometry.len() {
        result.push(Vec::with_capacity(len));
    }
    for mut dest in dest.into_iter() {
        for chunk_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(chunk_idx);
            let (chunk, rest) = dest.split_at_mut(chunk_size);
            dest = rest;
            result[chunk_idx].push(chunk);
        }
        assert!(dest.is_empty());
    }

    assert_eq!(geometry.len(), result.len());
    for el in result.iter() {
        assert_eq!(el.len(), len);
    }

    result
}

pub(crate) fn apply_row_wise<'a, A: 'static + Send + Sync, B: 'static + Send + Sync>(
    destination: Vec<&'a mut [A]>,
    extension_destination: Vec<&'a mut [B]>,
    trace_len: usize,
    worker: &Worker,
    func: impl Fn(Vec<&mut [A]>, Vec<&mut [B]>, usize, usize) + Sync,
) {
    let d_len = destination.len();
    let ext_d_len = extension_destination.len();
    worker.scope(trace_len, |scope, geometry| {
        let mut destination_chunks = split_destinations(destination, geometry);
        let mut destination_chunks = destination_chunks.drain(..).into_iter();
        let mut extension_destination_chunks = split_destinations(extension_destination, geometry);
        let mut extension_destination_chunks = extension_destination_chunks.drain(..).into_iter();
        let func_ref = &func;
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);

            let destination = destination_chunks.next().unwrap();
            debug_assert_eq!(destination.len(), d_len);
            let extension_destination = extension_destination_chunks.next().unwrap();
            debug_assert_eq!(extension_destination.len(), ext_d_len);

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                (func_ref)(destination, extension_destination, chunk_start, chunk_size);
            });
        }
        assert!(destination_chunks.next().is_none());
        assert!(extension_destination_chunks.next().is_none());
    });
}

pub fn prove_configured_with_gkr<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_eval_data: GKRFullWitnessTrace<F, Global, Global>,
    setup_precomputations: &GKRSetupPrecomputations<F, T>,
    precomputations: &Twiddles<F, Global>,
    // TODO: Column major LDE precomputations
    lde_factor: usize,
    num_queries: usize,
    pow_bits: u32,
    trace_len: usize,
    worker: &Worker,
) -> (GKRProverData<F, E, T>, GKRProof<F, E>) {
    assert_eq!(compiled_circuit.trace_len, trace_len);
    assert_eq!(
        witness_eval_data.column_major_memory_trace[0].len(),
        trace_len
    );

    // first we would commit to the witness - WHIR commitment itself is just the same as FRI commitment

    // now we need to draw prove-local challenges, and in our case it's just a challenge for lookups, and challenge to batch all constraints
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] = [
        E::from_base(F::from_u32_unchecked(42)),
        E::from_base(F::from_u32_unchecked(127)),
        E::from_base(F::from_u32_unchecked(0xff)),
    ];

    let mut gkr_storage = GKRStorage::<F, E>::default();

    // Now we can use lookup challenges to preprocess tables into values like (column_0 + alpha * column_1 + ... + additive_part)
    let (
        preprocessed_range_check_16,
        preprocessed_timestamp_range_checks,
        preprocessed_generic_lookup,
    ) = setup_precomputations.preprocess_lookups(
        compiled_circuit,
        lookup_alpha,
        lookup_additive_part,
        trace_len,
        &mut gkr_storage,
        worker,
    );

    // now we should perform "forward" evaluation, and fill the GKR storage
    let num_layers = compiled_circuit.layers.len();
    let mut witness_eval_data = witness_eval_data;
    // Go from layer 0 to the end, and produce intermediate polynomials. We do not need to commit to them
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            compiled_circuit,
            external_challenges,
            &mut witness_eval_data,
            trace_len,
            &preprocessed_range_check_16,
            &preprocessed_timestamp_range_checks,
            &preprocessed_generic_lookup,
            lookup_additive_part,
            constraints_batch_challenge,
            worker,
        );
    }

    // we will eventually output results of accumulations of grand product and lookups, and should commit to them here

    // then we go "backward", by taking random point evaluation claims from the previous layer, and producing claims for the next layer

    todo!();
}
