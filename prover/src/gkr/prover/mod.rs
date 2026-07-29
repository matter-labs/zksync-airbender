use std::alloc::Global;
use std::collections::BTreeMap;

use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use cs::utils::split_timestamp;
use field::TwoAdicField;
use field::{Field, FieldExtension, PrimeField};
use transcript::Keccak256Transcript;
use worker::WorkerGeometry;

use super::*;
pub use crate::definitions::GKRExternalChallenges;
use crate::fft::Twiddles;
use crate::gkr::prover::debug_utils::compute_initial_sumcheck_claims;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::stages::commitment_utils;
use crate::gkr::prover::stages::commitment_utils::ColumnMajorCosetBoundTracePart;
use crate::gkr::prover::transcript_utils::{
    commit_field_els, draw_random_field_els, draw_random_field_els_with_pow,
};
use crate::gkr::prover::utils::flatten_merkle_caps_iter_into;
use crate::gkr::prover_config::{pow_bits, ProverConfig};
use crate::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRStorage};
use crate::gkr::sumcheck::eq_poly::*;
use crate::gkr::virtual_polys::range_check::materialize_virtual_range_check_setup_poly;
use crate::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use crate::gkr::whir::queries::BaseFieldQuery;
use crate::gkr::whir::{
    whir_fold, ColumnMajorBaseOracleForCoset, ColumnMajorBaseOracleForLDE, MaterializedCosets,
    WhirPolyCommitProof,
};
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::merkle_trees::{
    ColumnMajorMerkleTreeConstructor, MerkleTreeCapVarLength, PathQueriable, RSQueriable,
};
use crate::worker::Worker;
use common_constants::{TimestampScalar, TIMESTAMP_COLUMNS_NUM_BITS};
use cs::definitions::{GKRAddress, VirtualSetupPoly};
use std::sync::Arc;

mod debug_utils;
pub mod dimension_reduction;
pub mod forward_loop;
pub mod setup;
pub mod stages;
pub mod sumcheck_loop;
#[cfg(feature = "gkr_test_forge")]
pub mod test_forge;
pub mod transcript_utils;
pub mod utils;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CommitmentMode {
    SeparateMemoryAndWitness,
    MergedMemoryAndWitness,
    MergedAndPackedMemoryAndWitness {
        pack_log2: usize,
        external_challenges_pow_bits: u32,
        register_final_state: [crate::definitions::FinalRegisterValue; 32],
        final_pc: u32,
        final_timestamp: TimestampScalar,
    }, // this mode assumes that external challenges are not "external" anymore
}

/// How the RS codewords of the memory/witness base commitments are physically
/// stored/served during proving. Orthogonal to [`CommitmentMode`] (which fixes the
/// logical commitment structure and thus the transcript layout): both policies
/// produce a byte-identical proof for the same [`CommitmentMode`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RsCodewordSource {
    /// Materialize every LDE coset in RAM; intermediate (folded) oracles built
    /// monolithically. The historical default for the non-packed modes.
    InMemory,
    /// Keep only the compact monomial form and recompute the queried coset on
    /// demand (coset-by-coset); intermediate oracles built coset-by-coset. Memory
    /// light; the historical behavior of the packed mode.
    Recompute,
}

/// Wraps the setup commitment, decoupling how its RS codewords and Merkle tree are
/// stored from the prover configuration. `InMemory` is the representation used
/// today (RS codewords + tree both in RAM). `OnDisk` anticipates serving RS
/// codewords from a [`RSQueriable`] source and Merkle paths from an mmap'd on-disk
/// tree ([`ColumnMajorMerkleTreeConstructor::DiskPath`]); there is no on-disk
/// `RSQueriable` implementation yet, so that variant is not yet usable end-to-end.
pub enum SetupCommitment<'a, F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>> {
    /// RS codewords + Merkle tree both in memory (borrowed from the caller).
    InMemory(&'a ColumnMajorBaseOracleForLDE<F, T>),
    /// RS codewords served by a queryable source; Merkle paths served from an
    /// mmap'd on-disk tree. Not yet wired end-to-end (no on-disk `RSQueriable`).
    OnDisk {
        rs: Box<dyn RSQueriable<F>>,
        tree: T::DiskPath<'a>,
        values_per_leaf: usize,
        coset_size_log2: usize,
    },
}

impl<'a, F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
    SetupCommitment<'a, F, T>
{
    /// The commitment cap (goes into the transcript).
    pub fn get_cap(&self) -> MerkleTreeCapVarLength {
        match self {
            SetupCommitment::InMemory(oracle) => oracle.tree.get_cap(),
            SetupCommitment::OnDisk { tree, .. } => PathQueriable::<F>::get_cap(tree),
        }
    }

    /// The in-memory oracle whir_fold reads for batching + queries. The on-disk
    /// path is not wired into whir_fold yet (no on-disk `RSQueriable`).
    fn as_in_memory_oracle(&self) -> &ColumnMajorBaseOracleForLDE<F, T> {
        match self {
            SetupCommitment::InMemory(oracle) => oracle,
            SetupCommitment::OnDisk { .. } => {
                unimplemented!("on-disk setup commitment is not wired into whir_fold yet")
            }
        }
    }

    /// Round-0 base query for the setup set (offset-major leaf values + path).
    fn query_for_folded_index(&self, query_index: usize) -> (Vec<Vec<F>>, BaseFieldQuery<F, T>) {
        match self {
            SetupCommitment::InMemory(oracle) => {
                let (_coset, leaf, query) = oracle.query_for_folded_index(query_index);
                (leaf, query)
            }
            SetupCommitment::OnDisk { .. } => {
                unimplemented!("on-disk setup commitment queries are not implemented yet")
            }
        }
    }
}

/// Per-set recompute (coset-by-coset) sources for the memory/witness base
/// commitments, installed when [`RsCodewordSource::Recompute`] is active. `set_idx`
/// 0 = memory (or the merged mem+witness oracle in the merged/packed modes), 1 =
/// witness (separate mode only). `None` for a set means that set has no columns.
struct BaseRecomputeSources<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>> {
    mem: Option<CosetByCosetBaseCommitment<F, T>>,
    wit: Option<CosetByCosetBaseCommitment<F, T>>,
}

/// Build the "slim" base oracle (only the main evaluation domain columns + the
/// commitment cap tree) that whir_fold reads for batching, from a coset-by-coset
/// base commitment. Round-0 queries for this oracle are served on demand by the
/// commitment via the base query hook.
fn slim_oracle_from_base_commitment<F, T>(
    commitment: &CosetByCosetBaseCommitment<F, T>,
    twiddles: &Twiddles<F, Global>,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); F::DEGREE]: Sized,
{
    let cap = commitment.get_cap();
    let coset0 = ColumnMajorBaseOracleForCoset {
        original_values_normal_order: commitment
            .main_domain_columns(twiddles, worker)
            .into_iter()
            .map(|col| ColumnMajorCosetBoundTracePart {
                column: Arc::new(col),
                offset: F::ONE,
            })
            .collect(),
        offset: F::ONE,
        coset_size_log2: commitment.trace_len_log2,
    };
    ColumnMajorBaseOracleForLDE {
        cosets: Box::new(MaterializedCosets {
            cosets: vec![coset0],
        }),
        tree: T::build_over_leaf_hashes(cap.cap.clone(), cap.cap.len(), worker),
        values_per_leaf: commitment.values_per_leaf,
        coset_size_log2: commitment.trace_len_log2,
    }
}

pub(crate) struct SendPtr<T: Sized>(*mut T);
unsafe impl<T: Send + Sync> Send for SendPtr<T> {}

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
    pub inits_and_teardowns_top_bits: Vec<u32>,
    pub lookup_challenges_pow_nonce: u64,
    pub batched_proximity_check_pow_nonce: u64,
    #[serde(default)]
    pub intermediate_transcript_seed: Option<[u8; 32]>,
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
pub struct WhirSchedule {
    pub base_lde_factor: usize,
    pub cap_size: usize,
    pub whir_steps_schedule: Vec<usize>,
    pub whir_queries_schedule: Vec<usize>,
    pub whir_steps_lde_factors: Vec<usize>,
    pub whir_pow_schedule: Vec<u32>,
}

impl WhirSchedule {
    pub fn total_queries(&self) -> usize {
        self.whir_queries_schedule.iter().sum()
    }

    pub fn total_poly_size_reduction(&self) -> usize {
        self.whir_steps_schedule.iter().sum()
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

/// Backward-compatible entry point: takes the in-memory setup commitment directly
/// and selects the RS-codeword storage policy that reproduces the historical,
/// mode-dependent behavior (packed mode recomputes; the others materialize). Use
/// [`prove_configured_with_gkr_with_storage`] to override the storage policy.
pub fn prove_configured_with_gkr<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    TR: ::transcript::Transcript<F, E>,
>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_eval_data: GKRFullWitnessTrace<F, Global, Global>,
    setup: &GKRSetup<F>,
    setup_commitment: &ColumnMajorBaseOracleForLDE<F, T>,
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    commitment_mode: CommitmentMode,
    inits_and_teardowns_top_bits: Vec<u32>,
    trace_len: usize,
    worker: &Worker,
) -> GKRProof<F, E, T>
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized,
{
    // Preserve the historical, mode-dependent storage policy for existing callers.
    let rs_codeword_source = match commitment_mode {
        CommitmentMode::MergedAndPackedMemoryAndWitness { .. } => RsCodewordSource::Recompute,
        CommitmentMode::SeparateMemoryAndWitness | CommitmentMode::MergedMemoryAndWitness => {
            RsCodewordSource::InMemory
        }
    };
    prove_configured_with_gkr_impl::<F, E, T, TR>(
        compiled_circuit,
        external_challenges,
        witness_eval_data,
        setup,
        &SetupCommitment::InMemory(setup_commitment),
        twiddles,
        prover_config,
        commitment_mode,
        rs_codeword_source,
        inits_and_teardowns_top_bits,
        trace_len,
        worker,
    )
}

/// Config-aware entry point: the caller chooses how the memory/witness RS
/// codewords are stored ([`RsCodewordSource`]) and wraps the setup commitment in
/// [`SetupCommitment`] (in-memory or on-disk). For a given [`CommitmentMode`] the
/// resulting proof is independent of these storage choices.
#[allow(clippy::too_many_arguments)]
pub fn prove_configured_with_gkr_with_storage<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    TR: ::transcript::Transcript<F, E>,
>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_eval_data: GKRFullWitnessTrace<F, Global, Global>,
    setup: &GKRSetup<F>,
    setup_commitment: &SetupCommitment<F, T>,
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    commitment_mode: CommitmentMode,
    rs_codeword_source: RsCodewordSource,
    inits_and_teardowns_top_bits: Vec<u32>,
    trace_len: usize,
    worker: &Worker,
) -> GKRProof<F, E, T>
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized,
{
    prove_configured_with_gkr_impl::<F, E, T, TR>(
        compiled_circuit,
        external_challenges,
        witness_eval_data,
        setup,
        setup_commitment,
        twiddles,
        prover_config,
        commitment_mode,
        rs_codeword_source,
        inits_and_teardowns_top_bits,
        trace_len,
        worker,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_configured_with_gkr_impl<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    TR: ::transcript::Transcript<F, E>,
>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_eval_data: GKRFullWitnessTrace<F, Global, Global>,
    setup: &GKRSetup<F>,
    setup_commitment: &SetupCommitment<F, T>,
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    commitment_mode: CommitmentMode,
    rs_codeword_source: RsCodewordSource,
    inits_and_teardowns_top_bits: Vec<u32>,
    trace_len: usize,
    worker: &Worker,
) -> GKRProof<F, E, T>
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized,
{
    assert_eq!(compiled_circuit.trace_len, trace_len);
    if witness_eval_data.column_major_memory_trace.len() > 0 {
        assert_eq!(
            witness_eval_data.column_major_memory_trace[0].len(),
            trace_len
        );
    }
    if witness_eval_data.column_major_witness_trace.len() > 0 {
        assert_eq!(
            witness_eval_data.column_major_witness_trace[0].len(),
            trace_len
        );
    }

    assert_eq!(
        inits_and_teardowns_top_bits.len(),
        compiled_circuit.memory_layout.teardown_sets.len()
    );

    assert_eq!(
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.whir_schedule.whir_steps_schedule[0]
    );

    let mut external_challenges = *external_challenges;

    let (
        mut seed,
        mem_oracle,
        wit_oracle,
        lookup_challenges_pow_nonce,
        [lookup_alpha, lookup_additive_part],
        // Present only under `RsCodewordSource::Recompute`: the lazy (coset-by-coset)
        // base commitment(s) whose query hook serves round-0 base queries in
        // `whir_fold`. `None` means the base oracles are fully materialized.
        base_recompute,
    ) = match commitment_mode {
        CommitmentMode::SeparateMemoryAndWitness => {
            // first we would commit to the witness - WHIR commitment itself is just the same as FRI commitment
            let (mem_oracle, wit_oracle, base_recompute) = match rs_codeword_source {
                RsCodewordSource::InMemory => {
                    let (mem_oracle, wit_oracle) =
                        stages::initial_commit::commit_separate_memory_and_witness_subtrees::<F, T>(
                            &witness_eval_data,
                            twiddles,
                            prover_config.lde_factor,
                            prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                            prover_config.cap_size,
                            trace_len.trailing_zeros() as usize,
                            worker,
                        );
                    (mem_oracle, wit_oracle, None)
                }
                RsCodewordSource::Recompute => {
                    // Commit memory and witness separately, each coset-by-coset; keep
                    // only the compact commitment + a slim oracle (main domain + cap).
                    let whir_first_fold_step_log2 =
                        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize;
                    let commit_set =
                        |columns: &[Vec<F>]| -> Option<CosetByCosetBaseCommitment<F, T>> {
                            if columns.is_empty() {
                                return None;
                            }
                            let inputs: Vec<&[F]> = columns.iter().map(|c| &c[..]).collect();
                            Some(CosetByCosetBaseCommitment::<F, T>::commit(
                                &inputs,
                                twiddles,
                                prover_config.lde_factor,
                                whir_first_fold_step_log2,
                                prover_config.cap_size,
                                trace_len.trailing_zeros() as usize,
                                worker,
                            ))
                        };
                    let mem_commitment = commit_set(&witness_eval_data.column_major_memory_trace);
                    let wit_commitment = commit_set(&witness_eval_data.column_major_witness_trace);
                    let build_oracle =
                        |commitment: &Option<CosetByCosetBaseCommitment<F, T>>| match commitment {
                            Some(c) => slim_oracle_from_base_commitment(c, twiddles, worker),
                            None => ColumnMajorBaseOracleForLDE::empty(
                                prover_config.base_oracles_values_per_leaf,
                                trace_len.trailing_zeros() as usize,
                                prover_config.lde_factor,
                            ),
                        };
                    let mem_oracle = build_oracle(&mem_commitment);
                    let wit_oracle = build_oracle(&wit_commitment);
                    (
                        mem_oracle,
                        wit_oracle,
                        Some(BaseRecomputeSources {
                            mem: mem_commitment,
                            wit: wit_commitment,
                        }),
                    )
                }
            };

            let mut transcript_input = vec![];
            // we should commit all "external" variables,
            // that are still part of the circuit, even though they are not formally the public input

            // circuit sequence and delegation type
            transcript_input.extend_from_slice(&inits_and_teardowns_top_bits[..]);

            external_challenges.flatten_into_buffer(&mut transcript_input);

            // commit our setup
            if setup.hypercube_evals.len() > 0 {
                flatten_merkle_caps_iter_into(
                    Some(setup_commitment.get_cap()).into_iter(),
                    &mut transcript_input,
                );
            }

            // memory
            if compiled_circuit.memory_layout.total_width > 0 {
                flatten_merkle_caps_iter_into(
                    Some(mem_oracle.tree.get_cap()).into_iter(),
                    &mut transcript_input,
                );
            }

            // and witness
            if compiled_circuit.witness_layout.total_width > 0 {
                flatten_merkle_caps_iter_into(
                    Some(wit_oracle.tree.get_cap()).into_iter(),
                    &mut transcript_input,
                );
            }

            let mut seed =
                <TR as ::transcript::Transcript<F, E>>::commit_initial_u32(&transcript_input);

            // Now we need to draw prove-local challenges, and in our case it's just a challenge for lookups,
            // and challenge to batch all constraints. They are gated behind a proof-of-work; commit-before-draw
            // is satisfied by `commit_initial` above.
            let lookup_challenges_pow_bits = pow_bits::lookup_challenges_pow_bits(
                prover_config.security_level.security_bits(),
                pow_bits::lookup_identity_degree(compiled_circuit),
            );
            let (lookup_challenges_pow_nonce, challenges): (u64, Vec<E>) =
                draw_random_field_els_with_pow::<F, E, TR>(
                    &mut seed,
                    2,
                    lookup_challenges_pow_bits,
                    worker,
                );
            let [lookup_alpha, lookup_additive_part] = challenges.try_into().unwrap();

            (
                seed,
                mem_oracle,
                wit_oracle,
                lookup_challenges_pow_nonce,
                [lookup_alpha, lookup_additive_part],
                base_recompute,
            )
        }
        CommitmentMode::MergedMemoryAndWitness => {
            let (merged_oracle, base_recompute) = match rs_codeword_source {
                RsCodewordSource::InMemory => {
                    let merged_oracle =
                        stages::initial_commit::commit_merged_memory_and_witness_subtrees::<F, T>(
                            &witness_eval_data,
                            twiddles,
                            prover_config.lde_factor,
                            prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                            prover_config.cap_size,
                            trace_len.trailing_zeros() as usize,
                            worker,
                        );
                    (merged_oracle, None)
                }
                RsCodewordSource::Recompute => {
                    // Commit the union of memory+witness columns coset-by-coset (no
                    // packing), byte-identical to the materialized merged oracle.
                    let merged_inputs: Vec<&[F]> = witness_eval_data
                        .column_major_memory_trace
                        .iter()
                        .chain(witness_eval_data.column_major_witness_trace.iter())
                        .map(|el| &el[..])
                        .collect();
                    assert!(
                        !merged_inputs.is_empty(),
                        "merged memory+witness commitment requires at least one column"
                    );
                    let commitment = CosetByCosetBaseCommitment::<F, T>::commit(
                        &merged_inputs,
                        twiddles,
                        prover_config.lde_factor,
                        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                        prover_config.cap_size,
                        trace_len.trailing_zeros() as usize,
                        worker,
                    );
                    let merged_oracle =
                        slim_oracle_from_base_commitment(&commitment, twiddles, worker);
                    (
                        merged_oracle,
                        Some(BaseRecomputeSources {
                            mem: Some(commitment),
                            wit: None,
                        }),
                    )
                }
            };

            let mut transcript_input = vec![];
            // we should commit all "external" variables,
            // that are still part of the circuit, even though they are not formally the public input

            // circuit sequence and delegation type
            transcript_input.extend_from_slice(&inits_and_teardowns_top_bits[..]);

            external_challenges.flatten_into_buffer(&mut transcript_input);

            // commit our setup
            if setup.hypercube_evals.len() > 0 {
                flatten_merkle_caps_iter_into(
                    Some(setup_commitment.get_cap()).into_iter(),
                    &mut transcript_input,
                );
            }

            flatten_merkle_caps_iter_into(
                Some(merged_oracle.tree.get_cap()).into_iter(),
                &mut transcript_input,
            );

            let mut seed =
                <TR as ::transcript::Transcript<F, E>>::commit_initial_u32(&transcript_input);

            let lookup_challenges_pow_bits = pow_bits::lookup_challenges_pow_bits(
                prover_config.security_level.security_bits(),
                pow_bits::lookup_identity_degree(compiled_circuit),
            );
            let (lookup_challenges_pow_nonce, challenges): (u64, Vec<E>) =
                draw_random_field_els_with_pow::<F, E, TR>(
                    &mut seed,
                    2,
                    lookup_challenges_pow_bits,
                    worker,
                );
            let [lookup_alpha, lookup_additive_part] = challenges.try_into().unwrap();

            (
                seed,
                merged_oracle,
                ColumnMajorBaseOracleForLDE::empty(
                    prover_config.base_oracles_values_per_leaf,
                    trace_len.trailing_zeros() as usize,
                    prover_config.lde_factor,
                ),
                lookup_challenges_pow_nonce,
                [lookup_alpha, lookup_additive_part],
                base_recompute,
            )
        }
        CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2,
            external_challenges_pow_bits,
            register_final_state,
            final_pc,
            final_timestamp,
        } => {
            // in this mode we will re-derive external challenges.
            //
            // The packed polynomials are 2^(N + pack_log2) and their LDE codeword (x
            // base_lde_factor) is very large. `Recompute` builds a coset-by-coset
            // commitment (keeps only the packed monomial forms + the small top tree)
            // and hands `whir_fold` a "slim" base oracle (main domain + cap); round-0
            // base queries are served on demand by the query hook. `InMemory`
            // materializes the whole packed codeword; both yield the same proof.
            let merged_inputs: Vec<&[F]> = witness_eval_data
                .column_major_memory_trace
                .iter()
                .chain(witness_eval_data.column_major_witness_trace.iter())
                .map(|el| &el[..])
                .collect();
            let (merged_oracle, base_recompute) = match rs_codeword_source {
                RsCodewordSource::InMemory => {
                    let merged_oracle =
                        stages::initial_commit::commit_packed_merged_memory_and_witness_subtrees::<
                            F,
                            T,
                        >(
                            &witness_eval_data,
                            twiddles,
                            prover_config.lde_factor,
                            prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                            prover_config.cap_size,
                            trace_len.trailing_zeros() as usize,
                            pack_log2,
                            worker,
                        );
                    (merged_oracle, None)
                }
                RsCodewordSource::Recompute => {
                    let commitment = CosetByCosetBaseCommitment::<F, T>::commit_packed(
                        &merged_inputs,
                        twiddles,
                        prover_config.lde_factor,
                        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                        prover_config.cap_size,
                        trace_len.trailing_zeros() as usize,
                        pack_log2,
                        worker,
                    );
                    let merged_oracle =
                        slim_oracle_from_base_commitment(&commitment, twiddles, worker);
                    (
                        merged_oracle,
                        Some(BaseRecomputeSources {
                            mem: Some(commitment),
                            wit: None,
                        }),
                    )
                }
            };

            let mut transcript_input = vec![];
            // we should commit all "external" variables,
            // that are still part of the circuit, even though they are not formally the public input

            // register final state - flatten same way as full statement verifier,
            // and in general it can be flattened to (32+1) * 3 u32 words -> bytes without interpretation
            // for L1 verifier
            let mut registers_buffer = [0u32; 32 * 3];
            for reg_idx in 0..32 {
                let value = register_final_state[reg_idx].value;
                let (timestamp_low, timestamp_high) =
                    split_timestamp(register_final_state[reg_idx].last_access_timestamp);
                registers_buffer[reg_idx * 3] = value;
                registers_buffer[reg_idx * 3 + 1] = timestamp_low;
                registers_buffer[reg_idx * 3 + 2] = timestamp_high;
            }
            transcript_input.extend(registers_buffer);

            let mut final_pc_buffer = [0u32; 3];
            final_pc_buffer[0] = final_pc;
            final_pc_buffer[1] = split_timestamp(final_timestamp).0;
            final_pc_buffer[2] = split_timestamp(final_timestamp).1;
            transcript_input.extend(final_pc_buffer);

            // inits and teardown bits
            transcript_input.extend_from_slice(&inits_and_teardowns_top_bits[..]);

            // commit our setup
            if setup.hypercube_evals.len() > 0 {
                flatten_merkle_caps_iter_into(
                    Some(setup_commitment.get_cap()).into_iter(),
                    &mut transcript_input,
                );
            }

            flatten_merkle_caps_iter_into(
                Some(merged_oracle.tree.get_cap()).into_iter(),
                &mut transcript_input,
            );

            let mut seed =
                <TR as ::transcript::Transcript<F, E>>::commit_initial_u32(&transcript_input);

            let lookup_challenges_pow_bits = pow_bits::lookup_challenges_pow_bits(
                prover_config.security_level.security_bits(),
                pow_bits::lookup_identity_degree(compiled_circuit),
            );

            let pow_bits = core::cmp::max(lookup_challenges_pow_bits, external_challenges_pow_bits);

            let num_challenges = GKRExternalChallenges::<F, E>::TOTAL_CHALLENGES + 2;

            let (lookup_challenges_pow_nonce, challenges): (u64, Vec<E>) =
                draw_random_field_els_with_pow::<F, E, TR>(
                    &mut seed,
                    num_challenges,
                    pow_bits,
                    worker,
                );
            external_challenges = GKRExternalChallenges::from_slice(
                &challenges[..GKRExternalChallenges::<F, E>::TOTAL_CHALLENGES],
            );
            let [lookup_alpha, lookup_additive_part] = challenges
                [GKRExternalChallenges::<F, E>::TOTAL_CHALLENGES..]
                .try_into()
                .unwrap();

            (
                seed,
                merged_oracle,
                ColumnMajorBaseOracleForLDE::empty(
                    prover_config.base_oracles_values_per_leaf,
                    trace_len.trailing_zeros() as usize,
                    prover_config.lde_factor,
                ),
                lookup_challenges_pow_nonce,
                [lookup_alpha, lookup_additive_part],
                base_recompute,
            )
        }
    };

    // then GKR is the same until the end of backward pass and derivation of claims

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
        if inits_and_teardowns_top_bits.is_empty() == false {
            use crate::gkr::virtual_polys::init_and_teardown_base::materialize_virtual_inits_and_teardowns_base_address_setup_poly;
            let (low, high) = materialize_virtual_inits_and_teardowns_base_address_setup_poly::<
                F,
                Global,
                2,
            >(trace_len.trailing_zeros(), worker);
            gkr_storage.insert_base_field_at_layer(
                0,
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                BaseFieldPoly::new(low),
            );
            gkr_storage.insert_base_field_at_layer(
                0,
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                BaseFieldPoly::new(high),
            );
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
            &external_challenges,
            &mut witness_eval_data,
            &inits_and_teardowns_top_bits,
            trace_len,
            &preprocessed_generic_lookup,
            lookup_alpha,
            lookup_additive_part,
            decoder_lookup_fill_value,
            worker,
        );
    }

    #[cfg(feature = "gkr_self_checks")]
    assert!(debug_utils::check_logup_identity(
        compiled_circuit,
        &gkr_storage,
        worker
    ));

    // final trace size on which we output the polynomials in plain text
    let final_trace_size_log_2 = prover_config.sumcheck_explicit_output_size_log_2;

    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            compiled_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            worker,
        );

    #[cfg(feature = "gkr_self_checks")]
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
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
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
    commit_field_els::<F, E, TR>(&mut seed, &evals_flattened);

    let num_challenges = final_trace_size_log_2 + 1;
    let mut challenges = draw_random_field_els::<F, E, TR>(&mut seed, num_challenges);
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
        claim_initset,
        claim_teardownset,
    ) = compute_initial_sumcheck_claims(
        &gkr_storage,
        &evaluation_point,
        &dimension_reducing_inputs[&initial_layer_for_sumcheck],
        worker,
    );

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

    if let Some(k) = output_map.get(&OutputType::LookupTimestamps) {
        top_layer_claims.insert(k.output[0], claim_timechecknum);
        top_layer_claims.insert(k.output[1], claim_timecheckden);
    }

    if let Some(k) = output_map.get(&OutputType::GenericLookup) {
        top_layer_claims.insert(k.output[0], claim_lookupnum);
        top_layer_claims.insert(k.output[1], claim_lookupden);
    }

    if let Some(k) = output_map.get(&OutputType::InitsAndTeardownsProduct) {
        top_layer_claims.insert(k.output[0], claim_initset);
        top_layer_claims.insert(k.output[1], claim_teardownset);
    }

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
        let proof = sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer::<F, E, TR>(
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

    let address_high_bits_shift = if inits_and_teardowns_top_bits.len() > 0 {
        high_bits_offset_for_inits_and_teardowns::<2>(trace_len)
    } else {
        // not important
        0u32
    };

    // Backward loop: standard layer-by-layer sumcheck
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate().rev() {
        let proof = sumcheck_loop::evaluate_sumcheck_for_layer::<F, E, TR>(
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
            &inits_and_teardowns_top_bits[..],
            address_high_bits_shift,
            &external_challenges,
            &mut seed,
            worker,
        );
        sumcheck_intermediate_values.insert(layer_idx, proof);
    }

    drop(preprocessed_generic_lookup);

    let mut base_layer_z = points_for_claims_at_layer
        .get(&0)
        .expect("must have base layer point")
        .clone();

    let mut _eq_at_z: Box<[E]> = vec![].into_boxed_slice();
    #[cfg(feature = "gkr_self_checks")]
    {
        let mut eq_precomputed = make_eq_poly_in_full(&base_layer_z, worker);
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
        let Some(value) = claims_for_layers[&0].get(&key).copied() else {
            panic!("Missing claim for {:?}", key);
        };
        #[cfg(feature = "gkr_self_checks")]
        {
            let poly = gkr_storage.get_base_layer(key);
            let evaluation = evaluate_with_precomputed_eq::<F, E>(poly, &_eq_at_z[..]);
            assert_eq!(evaluation, value, "diverged for {:?}", key);
        }
        setup_polys_claims.push(value);
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
                    &base_layer_z,
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
                    &base_layer_z,
                    trace_len.trailing_zeros()
                )
            );
        }
    }
    drop(gkr_storage);

    // The WHIR batching challenge is gated behind a proof-of-work; the GKR sumcheck
    // transcript above already committed everything that feeds this draw. The bit count
    // scales with the number of batched base-oracle columns l, so it is
    // computed per-circuit here (and identically baked by the verifier generator).
    let batched_proximity_pow_bits = pow_bits::batched_proximity_check_pow_bits(
        prover_config.security_level.security_bits(),
        trace_len.trailing_zeros() as usize,
        prover_config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(compiled_circuit),
    );

    let mut trace_len_log2_for_whir = trace_len.trailing_zeros() as usize;

    // and for WHIR we may need to reshuffle/merge claims depending on the mode
    let (mem_polys_claims, wit_polys_claims, setup_polys_claims) = match commitment_mode {
        CommitmentMode::SeparateMemoryAndWitness => {
            (mem_polys_claims, wit_polys_claims, setup_polys_claims)
        }
        CommitmentMode::MergedMemoryAndWitness => {
            // just move all witness claims to the memory same order
            let mut merged_claims = mem_polys_claims;
            merged_claims.extend(wit_polys_claims);

            (merged_claims, Vec::new(), setup_polys_claims)
        }
        CommitmentMode::MergedAndPackedMemoryAndWitness { pack_log2, .. } => {
            // in the same manner - we should be consistent with how we packed polynomials.

            // NOTE: this only allows Keccak trascript, that doesn't buffer and instead hashes every time
            assert!(
                core::any::TypeId::of::<TR>() == core::any::TypeId::of::<Keccak256Transcript>()
            );

            // We already have all prover-controlled variables in the transcript, so we can just draw
            // extra coordinates' values here
            let extra_coordinates: Vec<E> = draw_random_field_els::<F, E, TR>(&mut seed, pack_log2);

            // now recursively merge
            let mut merged_claims = mem_polys_claims;
            merged_claims.extend(wit_polys_claims);

            let [merged_claims, setup_polys_claims] = [merged_claims, setup_polys_claims]
                .map(|input| merge_claims(&input, &extra_coordinates));

            // and we need to update claim point
            let mut new_claim_point = extra_coordinates;
            new_claim_point.extend_from_slice(&base_layer_z);

            base_layer_z = new_claim_point;
            trace_len_log2_for_whir += pack_log2;

            #[cfg(feature = "gkr_self_checks")]
            {
                use crate::gkr::prover::stages::commitment_utils::compute_column_major_monomial_form_from_main_domain;
                use crate::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;

                // Reconstruct every packed polynomial from the committed base oracle
                // and check that its multilinear evaluation at the (now extended)
                // claim point matches the merged claim we just derived. We take the
                // FIRST coset (offset == 1, i.e. the base evaluation domain), invert
                // its NTT to recover the packed poly's monomial coefficients, turn
                // those into hypercube evaluations, and evaluate at `base_layer_z`.
                assert_eq!(
                    mem_oracle.cosets.num_columns(),
                    merged_claims.len(),
                    "one committed packed column per merged claim"
                );
                let eq_at_point = make_eq_poly_in_full::<E>(&base_layer_z, worker);
                let eq_at_point = eq_at_point.last().expect("eq poly has a full layer");
                for (column_index, expected_claim) in merged_claims.iter().enumerate() {
                    // Reduce the base-domain column to monomial coefficients: evals
                    // need IFFT, monomials are already there.
                    let column = mem_oracle.cosets.main_domain_column(column_index);
                    let mut hypercube_evals = if column.is_monomials() {
                        column.into_owned()
                    } else {
                        compute_column_major_monomial_form_from_main_domain::<F, F, Global>(
                            column.as_slice(),
                            twiddles,
                        )
                    };
                    // monomials -> hypercube evaluations of the packed multilinear,
                    // then bit-reverse (the packing committed `evals_into_coeffs(bitrev(H))`,
                    // so the inverse is `coeffs_into_hypercube_evals` then `bitreverse`;
                    // this mirrors `whir_fold`'s own claim recomputation).
                    let size_log2 = hypercube_evals.len().trailing_zeros();
                    multivariate_coeffs_into_hypercube_evals(&mut hypercube_evals, size_log2);
                    crate::fft::bitreverse_enumeration_inplace(&mut hypercube_evals);
                    // re-evaluate at the extended claim point and compare
                    assert_eq!(hypercube_evals.len(), eq_at_point.len());
                    let reevaluated =
                        evaluate_with_precomputed_eq::<F, E>(&hypercube_evals, eq_at_point);
                    assert_eq!(
                        reevaluated, *expected_claim,
                        "packed-commitment self-check: reconstructed evaluation must match merged claim"
                    );
                }
            }

            (merged_claims, Vec::new(), setup_polys_claims)
        }
    };

    let (batched_proximity_check_pow_nonce, whir_batching_challenges): (u64, Vec<E>) =
        draw_random_field_els_with_pow::<F, E, TR>(
            &mut seed,
            1,
            batched_proximity_pow_bits,
            worker,
        );
    let whir_batching_challenge = whir_batching_challenges[0];

    // Under `RsCodewordSource::Recompute` the base oracles are "slim" (they don't
    // hold every LDE coset), so install a query hook that recomputes the queried
    // coset on demand from the per-set coset-by-coset commitments, and switch the
    // intermediate (folded) RS oracles to coset-by-coset too. `set_idx`: 0 = memory
    // (or the merged mem+witness oracle), 1 = witness (separate mode only), 2 =
    // setup (always the in-memory setup commitment). Sets with no columns are never
    // queried, so their recompute source may be `None`.
    let recompute_hook = base_recompute.as_ref().map(|sources| {
        move |set_idx: usize, query_index: usize| -> (Vec<Vec<F>>, BaseFieldQuery<F, T>) {
            match set_idx {
                0 => sources
                    .mem
                    .as_ref()
                    .expect("memory recompute source must exist when set 0 has columns")
                    .query_structured(query_index, twiddles, worker),
                1 => sources
                    .wit
                    .as_ref()
                    .expect("witness recompute source must exist when set 1 has columns")
                    .query_structured(query_index, twiddles, worker),
                2 => setup_commitment.query_for_folded_index(query_index),
                _ => unreachable!("only memory(0)/witness(1)/setup(2) base sets exist"),
            }
        }
    });
    let base_query_hook: Option<&dyn Fn(usize, usize) -> (Vec<Vec<F>>, BaseFieldQuery<F, T>)> =
        recompute_hook
            .as_ref()
            .map(|h| h as &dyn Fn(usize, usize) -> (Vec<Vec<F>>, BaseFieldQuery<F, T>));
    let intermediate_oracle_mode = if base_recompute.is_some() {
        crate::gkr::whir::WhirIntermediateOracleMode::CosetByCoset
    } else {
        crate::gkr::whir::WhirIntermediateOracleMode::Monolithic
    };

    let intermediate_transcript_seed =
        if core::any::TypeId::of::<TR>() == core::any::TypeId::of::<Keccak256Transcript>() {
            // some unsafe magic
            assert_eq!(
                core::any::TypeId::of::<F>(),
                core::any::TypeId::of::<::field::Proth120>()
            );
            assert_eq!(
                core::any::TypeId::of::<E>(),
                core::any::TypeId::of::<::field::Proth120>()
            );
            let seed_copy: <Keccak256Transcript as ::transcript::Transcript<
                ::field::Proth120,
                ::field::Proth120,
            >>::Seed = unsafe { core::mem::transmute_copy(&seed) };
            Some(seed_copy.0)
        } else {
            None
        };

    let whir_proof = whir_fold::<F, E, T, TR>(
        mem_oracle,
        mem_polys_claims,
        wit_oracle,
        wit_polys_claims,
        setup_commitment.as_in_memory_oracle(),
        setup_polys_claims,
        base_layer_z.clone(),
        whir_batching_challenge,
        &prover_config.whir_schedule,
        twiddles,
        seed,
        prover_config.whir_schedule.cap_size,
        trace_len_log2_for_whir,
        base_query_hook,
        intermediate_oracle_mode,
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

    let mut grand_product_accumulator_computed = write_set_computed;
    grand_product_accumulator_computed
        .mul_assign(&read_set_computed.inverse().expect("must not be zero"));

    // For circuits with inline inits/teardowns (the unified reduced-machine path),
    // the proof's I/T product is a separate output channel — fold it into the
    // accumulator so the caller can do `initial_contribution * accumulator == 1`
    // as a single check (mirroring the standalone i/t proof's role).
    if let Some(it_evals) = final_explicit_evaluations.get(&OutputType::InitsAndTeardownsProduct) {
        // here the numbering is read - write
        let [teardown_set_computed, init_set_computed] = it_evals.clone().map(|els| {
            let mut result = E::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }
            result
        });
        // accumulation is write/read
        grand_product_accumulator_computed.mul_assign(&init_set_computed);
        grand_product_accumulator_computed
            .mul_assign(&teardown_set_computed.inverse().expect("must not be zero"));
    }

    #[cfg(feature = "gkr_self_checks")]
    if let CommitmentMode::MergedAndPackedMemoryAndWitness {
        register_final_state,
        final_pc,
        final_timestamp,
        ..
    } = commitment_mode
    {
        // self-check, write set/read set
        let mut registers_buffer = [0u32; 32 * 3];
        for reg_idx in 0..32 {
            let value = register_final_state[reg_idx].value;
            let (timestamp_low, timestamp_high) =
                split_timestamp(register_final_state[reg_idx].last_access_timestamp);
            registers_buffer[reg_idx * 3] = value;
            registers_buffer[reg_idx * 3 + 1] = timestamp_low;
            registers_buffer[reg_idx * 3 + 2] = timestamp_high;
        }

        use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
        use cs::definitions::NUM_REGISTERS;

        let (final_ts_low, final_ts_high) = split_timestamp(final_timestamp);

        let (machine_state_read_set_contribution, machine_state_write_set_contribution) =
            prover::definitions::produce_initial_permutation_product_separate_contributions(
                unsafe {
                    core::mem::transmute::<_, &[(u32, (u32, u32)); NUM_REGISTERS]>(
                        &registers_buffer,
                    )
                },
                INITIAL_PC,
                split_timestamp(INITIAL_TIMESTAMP),
                final_pc,
                (final_ts_low, final_ts_high),
                &external_challenges,
            );

        let mut t = grand_product_accumulator_computed;
        t.mul_assign(
            &machine_state_read_set_contribution
                .inverse()
                .expect("non-zero"),
        );
        t.mul_assign(&machine_state_write_set_contribution);

        assert_eq!(t, E::ONE);
    }

    GKRProof {
        external_challenges: external_challenges,
        whir_proof,
        final_explicit_evaluations,
        sumcheck_intermediate_values,
        grand_product_accumulator_computed,
        inits_and_teardowns_top_bits: inits_and_teardowns_top_bits.to_vec(),
        lookup_challenges_pow_nonce,
        batched_proximity_check_pow_nonce,
        intermediate_transcript_seed,
    }
}

fn merge_claims<F: Field>(input: &[F], extra_coordinates: &[F]) -> Vec<F> {
    let pack_log2 = extra_coordinates.len();
    let mut result = vec![];
    for chunk in input.chunks(1 << pack_log2) {
        let mut input = if chunk.len() == 1 << pack_log2 {
            chunk.to_vec()
        } else {
            let mut padded = chunk.to_vec();
            padded.resize(1 << pack_log2, F::ZERO);

            padded
        };
        let mut buffer = vec![];
        // note `rev` on the coordiantes - we will later on concatenate
        // coordiantes, so first coordiante is MSB
        for merge_point in extra_coordinates.iter().rev() {
            for [a, b] in input.as_chunks::<2>().0 {
                // canonical interpolation a + (b - a) * r', consistent with the packing
                // that concatenates sub-polys in order (block 0 => a at coordinate 0)
                use crate::gkr::prover::sumcheck_loop::interpolate_linear;
                let t = interpolate_linear(*a, *b, merge_point);
                buffer.push(t);
            }

            core::mem::swap(&mut input, &mut buffer);
            buffer.clear();
        }
        assert_eq!(input.len(), 1);
        result.push(input[0]);
    }

    result
}

#[cfg(test)]
mod packing_merge_tests {
    use super::merge_claims;
    use crate::gkr::prover::stages::commitment_utils::pack_polys_parallel_from_hypercubes_to_monomials;
    use crate::gkr::sumcheck::eq_poly::{evaluate_with_precomputed_eq, make_eq_poly_in_full};
    use crate::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use rand::RngCore;
    use worker::Worker;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn rand_f(rng: &mut impl RngCore) -> F {
        F::from_u32_with_reduction(rng.next_u32())
    }

    fn rand_e(rng: &mut impl RngCore) -> E {
        let coeffs = [(); 4].map(|_| rand_f(rng));
        <E as FieldExtension<F>>::from_coeffs(coeffs)
    }

    /// Inverse of `pack_polys_parallel_from_hypercubes_to_monomials` for a single
    /// packed poly: turn the whole `(N + pack_log2)`-variate monomial vector back
    /// into hypercube evaluations. The forward transform is `bitreverse` then
    /// `multivariate_hypercube_evals_into_coeffs` over ALL variables, so the inverse
    /// is `multivariate_coeffs_into_hypercube_evals` then `bitreverse`. The vector is
    /// treated as one multilinear — it can NOT be split into per-sub-poly halves.
    fn packed_monomials_to_hypercube_evals(packed: &mut [F]) {
        let size_log2 = packed.len().trailing_zeros();
        multivariate_coeffs_into_hypercube_evals(packed, size_log2);
        crate::fft::bitreverse_enumeration_inplace(packed);
    }

    /// Concatenate two `2^N`-sized multilinear polys `a`, `b` into a single
    /// `(N + 1)`-variate multilinear poly `P` (block index = most significant
    /// coordinate, `P(x, 0) = a(x)`, `P(x, 1) = b(x)`) and check that `merge_claims`
    /// reproduces `P` at the extended point, agreeing with a naive dot product
    /// against the full `(N + 1)`-variate equality polynomial.
    #[test]
    fn concatenate_two_polys_merge_claims_matches_extended_eq() {
        let worker = Worker::new_with_num_threads(2);
        const N: usize = 4;
        let size = 1usize << N;

        let mut rng = rand::rng();

        // two independent multilinear polys in hypercube-evaluation form
        let a: Vec<F> = (0..size).map(|_| rand_f(&mut rng)).collect();
        let b: Vec<F> = (0..size).map(|_| rand_f(&mut rng)).collect();

        // 1) a single random N-coordinate point, and the claims `a(r)`, `b(r)`
        //    obtained as a dot product with the equality poly of `r`.
        let r: Vec<E> = (0..N).map(|_| rand_e(&mut rng)).collect();
        let eq_r_layers = make_eq_poly_in_full::<E>(&r, &worker);
        let eq_r = eq_r_layers.last().unwrap();
        assert_eq!(eq_r.len(), size);
        let claim_a = evaluate_with_precomputed_eq::<F, E>(&a, eq_r);
        let claim_b = evaluate_with_precomputed_eq::<F, E>(&b, eq_r);

        // 2) concatenate the two polys "as monomials" via the commitment helper.
        //    `pack_log2 = 1` merges the 2 sub-polys into one packed poly that is the
        //    monomial form of the single (N + 1)-variate multilinear `P`.
        let packed =
            pack_polys_parallel_from_hypercubes_to_monomials::<F>(&[&a[..], &b[..]], 1, &worker);
        assert_eq!(packed.len(), 1);
        let mut p_evals = packed.into_iter().next().unwrap();
        assert_eq!(p_evals.len(), 2 * size);

        // 3) go back to hypercube evaluations of the (N + 1)-variate poly `P` by
        //    inverting the transform over the WHOLE vector (the packed monomials mix
        //    all variables and can not be split into per-sub-poly halves).
        packed_monomials_to_hypercube_evals(&mut p_evals);
        // the round-trip must recover the concatenated sub-poly evaluations exactly:
        // block 0 (low half) is `a`, block 1 (high half) is `b`.
        assert_eq!(&p_evals[..size], &a[..], "block 0 must round-trip to `a`");
        assert_eq!(&p_evals[size..], &b[..], "block 1 must round-trip to `b`");

        // 4a) evaluation via `merge_claims`: merge the two claims at a random extra
        //     coordinate `r'` (canonical interpolation a(r) + (b(r) - a(r)) * r').
        let r_prime = rand_e(&mut rng);
        let merged = merge_claims::<E>(&[claim_a, claim_b], &[r_prime]);
        assert_eq!(merged.len(), 1);
        let merged = merged[0];

        // 4b) naive evaluation: dot product of `P`'s hypercube evaluations with the
        //     full (N + 1)-variate equality poly at the extended point. `make_eq_poly`
        //     treats `challenges[0]` as the MOST-significant index bit, so the block
        //     coordinate (the MSB of `P`) is listed first, followed by `r`. With the
        //     canonical interpolation the block challenge is exactly `r'`.
        let mut ext_point = Vec::with_capacity(N + 1);
        ext_point.push(r_prime);
        ext_point.extend_from_slice(&r);
        let eq_ext_layers = make_eq_poly_in_full::<E>(&ext_point, &worker);
        let eq_ext = eq_ext_layers.last().unwrap();
        assert_eq!(eq_ext.len(), 2 * size);
        let naive = evaluate_with_precomputed_eq::<F, E>(&p_evals, eq_ext);

        assert_eq!(
            merged, naive,
            "merge_claims must equal the naive extended-eq evaluation of the merged poly"
        );
    }
}
