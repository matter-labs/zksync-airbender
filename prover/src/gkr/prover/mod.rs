use std::alloc::Global;
use std::collections::BTreeMap;

use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::TwoAdicField;
use field::{Field, FieldExtension, PrimeField};
use worker::WorkerGeometry;

use super::*;
use crate::definitions::Transcript;
use crate::fft::Twiddles;
use crate::gkr::prover::debug_utils::compute_initial_sumcheck_claims;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::stages::stage1;
use crate::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use crate::gkr::prover::utils::flatten_merkle_caps_iter_into;
use crate::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRStorage};
use crate::gkr::sumcheck::eq_poly::*;
use crate::gkr::virtual_polys::range_check::materialize_virtual_range_check_setup_poly;
use crate::gkr::whir::{whir_fold, ColumnMajorBaseOracleForLDE, WhirPolyCommitProof};
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::merkle_trees::ColumnMajorMerkleTreeConstructor;
use crate::worker::Worker;
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::definitions::{GKRAddress, VirtualSetupPoly, NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES};

mod debug_utils;
pub mod dimension_reduction;
pub mod forward_loop;
pub mod setup;
pub mod stages;
pub mod sumcheck_loop;
pub mod transcript_utils;
pub mod utils;

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

#[serde_with::serde_as]
#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, E: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct SumcheckIntermediateProofValues<F: PrimeField, E: FieldExtension<F> + Field> {
    pub sumcheck_num_rounds: usize,
    pub internal_round_coefficients: Vec<[E; 4]>, // max quadratic gates
    #[serde_as(as = "Vec<(_, _)>")]
    pub final_step_evaluations: BTreeMap<GKRAddress, Vec<E>>,
    #[serde_as(as = "Vec<(_, _)>")]
    pub extra_evaluations_from_caching_relations: BTreeMap<GKRAddress, E>,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> SumcheckIntermediateProofValues<F, E> {
    pub fn estimate_size(&self) -> usize {
        self.internal_round_coefficients.len() * E::DEGREE * 4 * core::mem::size_of::<u32>()
            + self
                .final_step_evaluations
                .iter()
                .map(|(_, v)| E::DEGREE * core::mem::size_of::<u32>() * v.len())
                .sum::<usize>()
            + self.extra_evaluations_from_caching_relations.len()
                * E::DEGREE
                * core::mem::size_of::<u32>()
    }
}

#[serde_with::serde_as]
#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, E: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct GKRProof<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub external_challenges: GKRExternalChallenges<F, E>,
    #[serde_as(as = "Vec<(_, _)>")]
    pub final_explicit_evaluations: BTreeMap<OutputType, [Vec<E>; 2]>,
    #[serde_as(as = "Vec<(_, _)>")]
    pub sumcheck_intermediate_values: BTreeMap<usize, SumcheckIntermediateProofValues<F, E>>,
    pub whir_proof: WhirPolyCommitProof<F, E, T>,
    pub grand_product_accumulator_computed: E,
}

impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
    GKRProof<F, E, T>
{
    pub fn estimate_size(&self) -> usize {
        self.final_explicit_evaluations
            .iter()
            .map(|(_, v)| E::DEGREE * core::mem::size_of::<u32>() * (v[0].len() + v[1].len()))
            .sum::<usize>()
            + self
                .sumcheck_intermediate_values
                .iter()
                .map(|(_, v)| v.estimate_size())
                .sum::<usize>()
            + self.whir_proof.estimate_size()
    }
}

#[derive(Clone, Debug)]
pub struct WhirSchedule {
    pub base_lde_factor: usize,
    pub cap_size: usize,
    pub whir_steps_schedule: Vec<usize>,
    pub whir_queries_schedule: Vec<usize>,
    pub whir_steps_lde_factors: Vec<usize>,
    pub whir_pow_schedule: Vec<u32>,
}

impl WhirSchedule {
    pub fn default_for_tests_80_bits_20() -> Self {
        let mut new = Self {
            base_lde_factor: 2,
            cap_size: 16,
            whir_steps_schedule: vec![1, 4, 4, 4, 4],
            whir_pow_schedule: vec![24, 24, 24, 24, 24],
            whir_steps_lde_factors: vec![8, 64, 128, 128],
            whir_queries_schedule: vec![],
        };

        assert_eq!(
            new.whir_steps_lde_factors.len() + 1,
            new.whir_steps_schedule.len()
        );
        assert_eq!(new.whir_pow_schedule.len(), new.whir_steps_schedule.len());

        for (lde, pow) in Some(new.base_lde_factor)
            .iter()
            .chain(new.whir_steps_lde_factors.iter())
            .zip(new.whir_pow_schedule.iter())
        {
            let sec_bits = 80 - *pow;
            let bits_per_query = lde.trailing_zeros();
            let num_queries = (sec_bits * 120).div_ceil(bits_per_query * 100); // roughly extra 20% on top of conjecture. Latest paper decrease conjectured value by 5-10% depending on rate
            new.whir_queries_schedule.push(num_queries as usize);
        }

        new
    }

    pub fn default_for_tests_80_bits_22() -> Self {
        let mut new = Self {
            base_lde_factor: 2,
            cap_size: 16,
            whir_steps_schedule: vec![1, 4, 4, 4, 4, 2],
            whir_pow_schedule: vec![24, 24, 24, 24, 24, 24],
            whir_steps_lde_factors: vec![8, 64, 128, 128, 128],
            whir_queries_schedule: vec![],
        };

        assert_eq!(
            new.whir_steps_lde_factors.len() + 1,
            new.whir_steps_schedule.len()
        );
        assert_eq!(new.whir_pow_schedule.len(), new.whir_steps_schedule.len());

        for (lde, pow) in Some(new.base_lde_factor)
            .iter()
            .chain(new.whir_steps_lde_factors.iter())
            .zip(new.whir_pow_schedule.iter())
        {
            let sec_bits = 80 - *pow;
            let bits_per_query = lde.trailing_zeros();
            let num_queries = (sec_bits * 120).div_ceil(bits_per_query * 100); // roughly extra 20% on top of conjecture. Latest paper decrease conjectured value by 5-10% depending on rate
            new.whir_queries_schedule.push(num_queries as usize);
        }

        new
    }

    pub fn default_for_tests_80_bits_24() -> Self {
        let mut new = Self {
            base_lde_factor: 2,
            cap_size: 16,
            whir_steps_schedule: vec![1, 4, 4, 4, 4, 4],
            whir_pow_schedule: vec![24, 24, 24, 24, 24, 24],
            whir_steps_lde_factors: vec![8, 64, 128, 128, 128],
            whir_queries_schedule: vec![],
        };

        assert_eq!(
            new.whir_steps_lde_factors.len() + 1,
            new.whir_steps_schedule.len()
        );
        assert_eq!(new.whir_pow_schedule.len(), new.whir_steps_schedule.len());

        for (lde, pow) in Some(new.base_lde_factor)
            .iter()
            .chain(new.whir_steps_lde_factors.iter())
            .zip(new.whir_pow_schedule.iter())
        {
            let sec_bits = 80 - *pow;
            let bits_per_query = lde.trailing_zeros();
            let num_queries = (sec_bits * 120).div_ceil(bits_per_query * 100); // roughly extra 20% on top of conjecture. Latest paper decrease conjectured value by 5-10% depending on rate
            new.whir_queries_schedule.push(num_queries as usize);
        }

        new
    }
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
    whir_schedule: &WhirSchedule,
    inits_and_teardowns_top_bits: Option<u32>,
    trace_len: usize,
    worker: &Worker,
) -> GKRProof<F, E, T>
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
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
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
        Some(setup_commitment.tree.get_cap()).into_iter(),
        &mut transcript_input,
    );

    // memory
    flatten_merkle_caps_iter_into(
        Some(mem_oracle.tree.get_cap()).into_iter(),
        &mut transcript_input,
    );

    // and witness
    flatten_merkle_caps_iter_into(
        Some(wit_oracle.tree.get_cap()).into_iter(),
        &mut transcript_input,
    );

    let mut seed = Transcript::commit_initial(&transcript_input);

    // now we need to draw prove-local challenges, and in our case it's just a challenge for lookups, and challenge to batch all constraints
    let challenges: Vec<E> = draw_random_field_els(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();

    let mut gkr_storage = GKRStorage::<F, E>::default();

    // Now we can use lookup challenges to preprocess tables into values like (column_0 + alpha * column_1 + ...),
    // but without(!) additive term, so we can use the same values for both cached and copied values,
    // and other gates (like non-vectorized lookups)
    let (preprocessed_generic_lookup, decoder_lookup_fill_value) = setup
        .preprocess_generic_lookups(
            compiled_circuit,
            lookup_alpha,
            trace_len,
            &mut gkr_storage,
            worker,
        );
    // add virtual polys and make them material
    {
        gkr_storage.insert_base_field_at_layer(
            0,
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
            BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<F, Global, 16>(
                trace_len.trailing_zeros(),
            )),
        );
        gkr_storage.insert_base_field_at_layer(
            0,
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
            BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<
                F,
                Global,
                TIMESTAMP_COLUMNS_NUM_BITS,
            >(trace_len.trailing_zeros())),
        );
        if inits_and_teardowns_top_bits.is_some() {
            todo!();
        }
    }

    // now we should perform "forward" evaluation, and fill the GKR storage
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
            &preprocessed_generic_lookup,
            lookup_alpha,
            lookup_additive_part,
            decoder_lookup_fill_value,
            constraints_batch_challenge,
            worker,
        );
    }

    #[cfg(feature = "gkr_self_checks")]
    assert!(debug_utils::check_logup_identity(
        compiled_circuit,
        &gkr_storage,
        worker
    ));

    let final_trace_size_log_2 = 4;

    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            compiled_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            worker,
        );

    assert!(debug_utils::check_logup_identity_after_dimension_reduction(
        &dimension_reducing_inputs,
        &gkr_storage,
        worker
    ));

    println!("Forward sumcheck loop is done, outputing explicit small polynomials");

    // get final evaluations
    let mut final_explicit_evaluations = BTreeMap::new();
    let mut evals_flattened = vec![];
    for (k, v) in dimension_reducing_inputs[&initial_layer_for_sumcheck].iter() {
        match *k {
            OutputType::PermutationProduct => {
                let mut final_evals: [Vec<E>; 2] = std::array::from_fn(|_| Vec::new());
                for (i, addr) in v.output.iter().enumerate() {
                    let poly = gkr_storage.get_ext_poly(*addr);
                    assert_eq!(poly.len(), 1 << final_trace_size_log_2);
                    evals_flattened.extend_from_slice(poly);
                    final_evals[i] = poly.to_vec();
                }
                final_explicit_evaluations.insert(*k, final_evals);
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let [num, den] = v.output.clone().try_into().unwrap();
                let num = gkr_storage.get_ext_poly(num);
                evals_flattened.extend_from_slice(num);
                let den = gkr_storage.get_ext_poly(den);
                evals_flattened.extend_from_slice(den);
                final_explicit_evaluations.insert(*k, [num.to_vec(), den.to_vec()]);
            }
        }
    }
    commit_field_els(&mut seed, &evals_flattened);

    let num_challenges = final_trace_size_log_2 + 1;
    let mut challenges = draw_random_field_els::<F, E>(&mut seed, num_challenges);
    let batching_challenge = challenges.pop().unwrap();

    println!("Evaluating initial claims for sumcheck loop");

    let evaluation_point = challenges;
    let (
        claim_readset,
        claim_writeset,
        claim_rangechecknum,
        claim_rangecheckden,
        claim_timechecknum,
        claim_timecheckden,
        claim_lookupnum,
        claim_lookupden,
    ) = compute_initial_sumcheck_claims(
        &gkr_storage,
        &evaluation_point,
        &dimension_reducing_inputs[&initial_layer_for_sumcheck],
        worker,
    );

    // let output_map = &compiled_circuit.global_output_map;
    let mut top_layer_claims: BTreeMap<GKRAddress, E> = BTreeMap::new();
    let output_map = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct].output[0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct].output[1],
        claim_writeset,
    );
    if let Some(k) = output_map.get(&OutputType::Lookup16Bits) {
        top_layer_claims.insert(k.output[0], claim_rangechecknum);
        top_layer_claims.insert(k.output[1], claim_rangecheckden);
    }
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps].output[0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps].output[1],
        claim_timecheckden,
    );
    top_layer_claims.insert(
        output_map[&OutputType::GenericLookup].output[0],
        claim_lookupnum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::GenericLookup].output[1],
        claim_lookupden,
    );

    println!("Sumcheck loop is starting");

    // then we go "backward", by taking random point evaluation claims from the previous layer, and producing claims for the next layer
    let mut claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E>> = BTreeMap::new();
    let mut points_for_claims_at_layer = BTreeMap::new();

    claims_for_layers.insert(initial_layer_for_sumcheck + 1, top_layer_claims);
    points_for_claims_at_layer.insert(initial_layer_for_sumcheck + 1, evaluation_point);

    let mut sumcheck_intermediate_values = BTreeMap::new();

    let mut sumcheck_batching_challenge = batching_challenge;
    let mut reduced_trace_size_log_2 = final_trace_size_log_2;
    for (layer_idx, layer) in dimension_reducing_inputs.into_iter().rev() {
        let proof = sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer(
            layer_idx,
            &layer,
            &mut points_for_claims_at_layer,
            &mut claims_for_layers,
            &mut gkr_storage,
            &mut sumcheck_batching_challenge,
            &mut seed,
            1 << reduced_trace_size_log_2,
            worker,
        );
        sumcheck_intermediate_values.insert(layer_idx, proof);
        reduced_trace_size_log_2 += 1;
    }

    assert_eq!(1 << reduced_trace_size_log_2, trace_len);

    // Backward loop: standard layer-by-layer sumcheck
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate().rev() {
        let proof = sumcheck_loop::evaluate_sumcheck_for_layer(
            layer_idx,
            layer,
            &mut points_for_claims_at_layer,
            &mut claims_for_layers,
            &mut gkr_storage,
            &mut sumcheck_batching_challenge,
            compiled_circuit,
            trace_len,
            lookup_alpha,
            lookup_additive_part,
            constraints_batch_challenge,
            external_challenges,
            &mut seed,
            worker,
        );
        sumcheck_intermediate_values.insert(layer_idx, proof);
    }

    // let base_layer_z = points_for_claims_at_layer
    //     .get(&0)
    //     .expect("must have base layer point");

    // let eq_precomputed = make_eq_poly_in_full(base_layer_z, worker);
    // let eq_at_z = eq_precomputed.last().unwrap();

    // let layer_desc = &compiled_circuit.layers[0];
    // let base_layer_claims = claims_for_layers.entry(0).or_insert_with(BTreeMap::new);

    // for (cached_addr, relation) in layer_desc.cached_relations.iter() {
    //     debug_assert!(
    //         base_layer_claims.contains_key(cached_addr),
    //         "Missing claim for cached address {:?}",
    //         cached_addr
    //     );

    //     for dep in relation.dependencies() {
    //         if base_layer_claims.contains_key(&dep) {
    //             continue;
    //         }
    //         match dep {
    //             GKRAddress::BaseLayerWitness(_)
    //             | GKRAddress::BaseLayerMemory(_)
    //             | GKRAddress::Setup(_) => {
    //                 println!("Explicitly computing value for {:?}", dep);
    //                 let values = gkr_storage.get_base_layer(dep);
    //                 let evaluation = evaluate_with_precomputed_eq::<F, E>(values, &eq_at_z[..]);
    //                 base_layer_claims.insert(dep, evaluation);
    //             }
    //             _ => {
    //                 panic!(
    //                     "Unexpected dependency address {:?} for cached relation {:?}",
    //                     dep, cached_addr
    //                 );
    //             }
    //         }
    //     }
    // }

    // #[cfg(feature = "gkr_self_checks")]
    // assert!(debug_utils::verify_cache_relations(
    //     layer_desc,
    //     &base_layer_claims,
    //     external_challenges,
    // ));

    drop(preprocessed_generic_lookup);

    let base_layer_z = points_for_claims_at_layer
        .get(&0)
        .expect("must have base layer point");

    let mut _eq_at_z: Box<[E]> = vec![].into_boxed_slice();
    #[cfg(feature = "gkr_self_checks")]
    {
        let mut eq_precomputed = make_eq_poly_in_full(base_layer_z, worker);
        _eq_at_z = eq_precomputed.pop().unwrap();
    }

    let mut mem_polys_claims = Vec::with_capacity(compiled_circuit.memory_layout.total_width);
    for i in 0..compiled_circuit.memory_layout.total_width {
        let key = GKRAddress::BaseLayerMemory(i);
        let Some(value) = claims_for_layers[&0].get(&key).copied() else {
            panic!("Missing claim for {:?}", key);
        };
        #[cfg(feature = "gkr_self_checks")]
        {
            let poly = gkr_storage.get_base_layer(key);
            let evaluation = evaluate_with_precomputed_eq::<F, E>(poly, &_eq_at_z[..]);
            assert_eq!(evaluation, value, "diverged for {:?}", key);
        }
        mem_polys_claims.push(value);
    }
    let mut wit_polys_claims = Vec::with_capacity(compiled_circuit.witness_layout.total_width);
    for i in 0..compiled_circuit.witness_layout.total_width {
        let key = GKRAddress::BaseLayerWitness(i);
        let Some(value) = claims_for_layers[&0].get(&key).copied() else {
            panic!("Missing claim for {:?}", key);
        };
        #[cfg(feature = "gkr_self_checks")]
        {
            let poly = gkr_storage.get_base_layer(key);
            let evaluation = evaluate_with_precomputed_eq::<F, E>(poly, &_eq_at_z[..]);
            assert_eq!(evaluation, value, "diverged for {:?}", key);
        }
        wit_polys_claims.push(value);
    }
    let mut setup_polys_claims = Vec::with_capacity(setup.hypercube_evals.len());
    for i in 0..setup.hypercube_evals.len() {
        let key = GKRAddress::Setup(i);
        if let Some(value) = claims_for_layers[&0].get(&key).copied() {
            #[cfg(feature = "gkr_self_checks")]
            {
                let poly = gkr_storage.get_base_layer(key);
                let evaluation = evaluate_with_precomputed_eq::<F, E>(poly, &_eq_at_z[..]);
                assert_eq!(evaluation, value, "diverged for {:?}", key);
            }
            setup_polys_claims.push(value);
        } else {
            // we have rare case when setup poly is not used, but we keep setup logic simple,
            // we have rare case when setup poly is not used, but we keep setup logic simple,
            // and so we have to re-evaluate it
            let poly = gkr_storage.get_base_layer(key);
            let evaluation = evaluate_with_precomputed_eq::<F, E>(poly, &_eq_at_z[..]);
            setup_polys_claims.push(evaluation);
        }
    }

    #[cfg(feature = "gkr_self_checks")]
    {
        if let Some(value) = claims_for_layers[&0]
            .get(&GKRAddress::VirtualSetup(
                VirtualSetupPoly::RangeCheck16Bits,
            ))
            .copied()
        {
            use crate::gkr::virtual_polys::range_check::evaluate_virtual_range_check_setup_poly;
            assert_eq!(
                value,
                evaluate_virtual_range_check_setup_poly::<F, E, 16>(
                    base_layer_z,
                    trace_len.trailing_zeros()
                )
            );
        }
        if let Some(value) = claims_for_layers[&0]
            .get(&GKRAddress::VirtualSetup(
                VirtualSetupPoly::RangeCheckTimestamp,
            ))
            .copied()
        {
            use crate::gkr::virtual_polys::range_check::evaluate_virtual_range_check_setup_poly;
            assert_eq!(
                value,
                evaluate_virtual_range_check_setup_poly::<F, E, TIMESTAMP_COLUMNS_NUM_BITS>(
                    base_layer_z,
                    trace_len.trailing_zeros()
                )
            );
        }
    }

    drop(gkr_storage);

    let whir_batching_challenge = draw_random_field_els::<F, E>(&mut seed, 1);
    let whir_batching_challenge = whir_batching_challenge[0];

    let WhirSchedule {
        base_lde_factor,
        cap_size,
        whir_steps_schedule,
        whir_queries_schedule,
        whir_steps_lde_factors,
        whir_pow_schedule,
    } = whir_schedule.clone();

    let whir_proof = whir_fold(
        mem_oracle,
        mem_polys_claims,
        wit_oracle,
        wit_polys_claims,
        setup_commitment,
        setup_polys_claims,
        base_layer_z.clone(),
        base_lde_factor,
        whir_batching_challenge,
        whir_steps_schedule,
        whir_queries_schedule,
        whir_steps_lde_factors,
        whir_pow_schedule,
        twiddles,
        seed,
        cap_size,
        trace_len.trailing_zeros() as usize,
        worker,
    );

    let [read_set_computed, write_set_computed] = final_explicit_evaluations
        .get(&OutputType::PermutationProduct)
        .expect("must be present")
        .clone()
        .map(|els| {
            let mut result = E::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }

            result
        });

    let mut grand_product_accumulator_computed = read_set_computed;
    grand_product_accumulator_computed
        .mul_assign(&write_set_computed.inverse().expect("must not be zero"));

    GKRProof {
        external_challenges: *external_challenges,
        whir_proof,
        final_explicit_evaluations,
        sumcheck_intermediate_values,
        grand_product_accumulator_computed,
    }
}
