use std::alloc::Global;
use std::collections::BTreeMap;

use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::TwoAdicField;
use field::{Field, FieldExtension, PrimeField};
use worker::WorkerGeometry;

use super::*;
use crate::definitions::Transcript;
use crate::fft::Twiddles;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::stages::stage1;
use crate::gkr::prover::transcript_utils::draw_random_field_els;
use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::whir::{whir_fold, ColumnMajorBaseOracleForLDE};
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::merkle_trees::ColumnMajorMerkleTreeConstructor;
use crate::merkle_trees::MerkleTreeCapVarLength;
use crate::prover_stages::flatten_merkle_caps_iter_into;
use crate::worker::Worker;

use cs::definitions::{GKRAddress, NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES};

mod debug_utils;
pub mod forward_loop;
pub mod setup;
pub mod stages;
pub mod sumcheck_loop;
pub mod transcript_utils;

pub(crate) struct SendPtr<T: Sized>(*mut T);
unsafe impl<T: Send + Sync> Send for SendPtr<T> {}

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

impl<F: PrimeField, E: FieldExtension<F> + Field> GKRExternalChallenges<F, E> {
    pub fn flatten_into_buffer(&self, dst: &mut Vec<u32>)
    where
        [(); E::DEGREE]: Sized,
    {
        use crate::gkr::prover::transcript_utils::flatten_field_els_into;
        flatten_field_els_into(&self.permutation_argument_linearization_challenges, dst);
        flatten_field_els_into(&[self.permutation_argument_additive_part], dst);
    }
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
    setup: &GKRSetup<F>,
    setup_commitment: &ColumnMajorBaseOracleForLDE<F, T>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    num_queries: usize,
    pow_bits: u32,
    inits_and_teardowns_top_bits: Option<u32>,
    trace_len: usize,
    worker: &Worker,
) -> (GKRProverData<F, E, T>, GKRProof<F, E>)
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized,
{
    assert_eq!(compiled_circuit.trace_len, trace_len);
    assert_eq!(
        witness_eval_data.column_major_memory_trace[0].len(),
        trace_len
    );

    // first we would commit to the witness - WHIR commitment itself is just the same as FRI commitment
    let (mem_oracle, wit_oracle) = stage1::stage1::<F, T>(
        &witness_eval_data,
        twiddles,
        lde_factor,
        lde_factor.trailing_zeros() as usize,
        1,
        trace_len.trailing_zeros() as usize,
        worker,
    );

    let mut transcript_input = vec![];
    // we should commit all "external" variables,
    // that are still part of the circuit, even though they are not formally the public input

    // circuit sequence and delegation type
    if let Some(inits_and_teardowns_top_bits) = inits_and_teardowns_top_bits {
        transcript_input.push(inits_and_teardowns_top_bits);
    }

    external_challenges.flatten_into_buffer(&mut transcript_input);

    // commit our setup
    flatten_merkle_caps_iter_into(
        setup_commitment.cosets.iter().map(|el| el.tree.get_cap()),
        &mut transcript_input,
    );

    // memory
    flatten_merkle_caps_iter_into(
        mem_oracle.cosets.iter().map(|el| el.tree.get_cap()),
        &mut transcript_input,
    );

    // and witness
    flatten_merkle_caps_iter_into(
        wit_oracle.cosets.iter().map(|el| el.tree.get_cap()),
        &mut transcript_input,
    );

    let mut seed = Transcript::commit_initial(&transcript_input);

    // now we need to draw prove-local challenges, and in our case it's just a challenge for lookups, and challenge to batch all constraints
    let challenges: Vec<E> = draw_random_field_els(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();
    // let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] = [
    //     E::from_base(F::from_u32_unchecked(42)),
    //     E::from_base(F::from_u32_unchecked(127)),
    //     E::from_base(F::from_u32_unchecked(0xff)),
    // ];

    let mut gkr_storage = GKRStorage::<F, E>::default();

    // Now we can use lookup challenges to preprocess tables into values like (column_0 + alpha * column_1 + ... + additive_part)
    let (
        preprocessed_range_check_16,
        preprocessed_timestamp_range_checks,
        preprocessed_generic_lookup,
    ) = setup.preprocess_lookups(
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

    debug_assert!(debug_utils::check_logup_identity(
        compiled_circuit,
        &gkr_storage,
        worker
    ));

    let (
        claim_readset,
        claim_writeset,
        claim_rangechecknum,
        claim_rangecheckden,
        claim_timechecknum,
        claim_timecheckden,
        claim_lookupnum,
        claim_lookupden,
        evaluation_point,
    ) = debug_utils::mock_output_claims(compiled_circuit, &gkr_storage, trace_len);

    let output_map = &compiled_circuit.global_output_map;
    let mut top_layer_claims: BTreeMap<GKRAddress, E> = BTreeMap::new();

    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct][0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct][1],
        claim_writeset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::Lookup16Bits][0],
        claim_rangechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::Lookup16Bits][1],
        claim_rangecheckden,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps][0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps][1],
        claim_timecheckden,
    );
    top_layer_claims.insert(output_map[&OutputType::GenericLookup][0], claim_lookupnum);
    top_layer_claims.insert(output_map[&OutputType::GenericLookup][1], claim_lookupden);

    // then we go "backward", by taking random point evaluation claims from the previous layer, and producing claims for the next layer
    let mut claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    let mut points_for_claims_at_layer = BTreeMap::new();

    claims_for_layers.insert(compiled_circuit.layers.len(), top_layer_claims);
    points_for_claims_at_layer.insert(compiled_circuit.layers.len(), evaluation_point);

    // Backward loop: standard layer-by-layer sumcheck
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate().rev() {
        sumcheck_loop::evaluate_sumcheck_for_layer(
            layer_idx,
            layer,
            &mut points_for_claims_at_layer,
            &mut claims_for_layers,
            &mut gkr_storage,
            compiled_circuit,
            external_challenges,
            trace_len,
            lookup_additive_part,
            constraints_batch_challenge,
            worker,
        );
    }

    let base_layer_z = points_for_claims_at_layer
        .get(&0)
        .expect("must have base layer point");

    use crate::gkr::sumcheck::eq_poly::*;
    let eq_precomputed = make_eq_poly_in_full::<E>(base_layer_z);
    let eq_at_z = eq_precomputed.last().unwrap();

    let layer_desc = &compiled_circuit.layers[0];
    let base_layer_claims = claims_for_layers.entry(0).or_insert_with(BTreeMap::new);

    for (cached_addr, relation) in layer_desc.cached_relations.iter() {
        debug_assert!(
            base_layer_claims.contains_key(cached_addr),
            "Missing claim for cached address {:?}",
            cached_addr
        );

        for dep in relation.dependencies() {
            if base_layer_claims.contains_key(&dep) {
                continue;
            }
            match dep {
                GKRAddress::BaseLayerWitness(_)
                | GKRAddress::BaseLayerMemory(_)
                | GKRAddress::Setup(_) => {
                    let values = gkr_storage.get_base_layer(dep);
                    let evaluation = evaluate_with_precomputed_eq::<F, E>(values, &eq_at_z[..]);
                    base_layer_claims.insert(dep, evaluation);
                }
                _ => {
                    panic!(
                        "Unexpected dependency address {:?} for cached relation {:?}",
                        dep, cached_addr
                    );
                }
            }
        }
    }

    debug_assert!(debug_utils::verify_cache_relations(
        layer_desc,
        &base_layer_claims,
        external_challenges,
    ));

    drop(gkr_storage);
    drop(preprocessed_range_check_16);
    drop(preprocessed_timestamp_range_checks);
    drop(preprocessed_generic_lookup);

    let mut mem_polys_claims = Vec::with_capacity(compiled_circuit.memory_layout.total_width);
    for i in 0..compiled_circuit.memory_layout.total_width {
        let key = GKRAddress::BaseLayerMemory(i);
        let Some(value) = claims_for_layers[&0].get(&key).copied() else {
            panic!("Missing claim for {:?}", key);
        };
        mem_polys_claims.push(value);
    }
    let mut wit_polys_claims = Vec::with_capacity(compiled_circuit.witness_layout.total_width);
    for i in 0..compiled_circuit.witness_layout.total_width {
        let key = GKRAddress::BaseLayerWitness(i);
        let Some(value) = claims_for_layers[&0].get(&key).copied() else {
            panic!("Missing claim for {:?}", key);
        };
        wit_polys_claims.push(value);
    }
    let mut setup_polys_claims = Vec::with_capacity(setup.hypercube_evals.len());
    for i in 0..setup.hypercube_evals.len() {
        let key = GKRAddress::Setup(i);
        let Some(value) = claims_for_layers[&0].get(&key).copied() else {
            panic!("Missing claim for {:?}", key);
        };
        setup_polys_claims.push(value);
    }
    let original_evaluation_point = points_for_claims_at_layer[&0].clone();

    let whir_batching_challenge = draw_random_field_els::<F, E>(&mut seed, 1);
    let whir_batching_challenge = whir_batching_challenge[0];

    todo!();

    // let whir_proof = whir_fold(
    //     mem_oracle,
    //     mem_polys_claims,
    //     wit_oracle,
    //     wit_polys_claims,
    //     setup_commitment,
    //     setup_polys_claims,
    //     original_evaluation_point,
    //     lde_factor,
    //     whir_batching_challenge,
    //     whir_steps_schedule,
    //     whir_queries_schedule,
    //     whir_steps_lde_factors,
    //     whir_pow_schedule,
    //     twiddles,
    //     seed,
    //     tree_cap_size,
    //     trace_len.trailing_zeros() as usize,
    //     worker
    // );

    // todo!();
}
