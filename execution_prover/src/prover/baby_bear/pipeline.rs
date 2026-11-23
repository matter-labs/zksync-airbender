mod cache_seed;
mod results;

use super::*;
use cache_seed::seed_from_cache;
use results::{
    dispatch_backend_requests, maybe_close_request_sender_after_progress, RequestContext,
    ResultAccumulator,
};

impl<B: ExecutionBackend> ExecutionProver<B> {
    pub(super) fn get_result<ND: NonDeterminismCSRSource + Send + 'static>(
        &self,
        proving: bool,
        request_partial_trees: bool,
        cache: &mut Option<TraceCache<B::Allocator>>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: ND,
        pow_challenge: u64,
        external_challenges: Option<GKRExternalChallenges<BF, E4>>,
        proof_caps: BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
        mut proof_partial_trees: BTreeMap<(CircuitType, usize), MemoryPartialTrees<B::Allocator>>,
        profile: ProofProfile,
    ) -> (ExecutionProverResult<B::Allocator>, ND) {
        if let Some(cache) = cache.as_ref() {
            if proving {
                assert!(cache.simulation_result.is_some());
            } else {
                assert!(cache.is_not_initialized());
            }
        }
        assert!(proving ^ external_challenges.is_none());
        let binary_holder = &self.binary_holders[&binary_key];
        assert!(
            !binary_holder.execution_kind.is_l1_wrap(),
            "ExecutionKind::{:?} requires prove_l1_wrap",
            binary_holder.execution_kind
        );
        assert!(
            binary_holder.profiles.contains(&profile),
            "ProofProfile::{profile:?} was not declared for this binary"
        );
        let commitment_mode = crate::config::execution_commitment_mode(
            binary_holder.execution_kind,
            profile,
            self.configuration.soundness_mode,
            |circuit| binary_holder.compiled_circuit(circuit),
        );
        let (work_results_sender, work_results_receiver) = unbounded();
        let (work_requests_sender, work_requests_receiver) = unbounded();
        let work_batch = WorkBatch {
            batch_id,
            receiver: work_requests_receiver,
            sender: work_results_sender.clone(),
        };
        trace!("BATCH[{batch_id}] PROVER sending work batch to backend");
        self.backend.submit(work_batch);
        let cache_seed = seed_from_cache(
            self,
            binary_holder,
            proving,
            cache,
            batch_id,
            external_challenges.as_ref(),
            &proof_caps,
            &mut proof_partial_trees,
            &work_requests_sender,
            profile,
        );
        let mut sent_requests_count = cache_seed.sent_requests_count;
        let requests_served_from_cache = cache_seed.requests_served_from_cache;
        let trivial_unified_inits_and_teardowns = cache_seed.trivial_unified_inits_and_teardowns;
        let mut work_requests_sender = Some(work_requests_sender);
        let execution_kind = binary_holder.execution_kind;
        let machine_type = binary_holder.machine_type;
        let abort = Arc::new(AtomicBool::new(false));
        let mut acc = ResultAccumulator::new();
        acc.pending_requests_count = cache_seed.pending_requests_count;
        acc.trivial_unified_inits_and_teardowns_count =
            cache_seed.trivial_unified_inits_and_teardowns_count;
        let mut abort_signaled = if let Some(cache) = cache.as_ref() {
            if proving && cache.total_requests_count == sent_requests_count {
                work_requests_sender = None;
                acc.simulation_result = cache.simulation_result.clone();
                true
            } else {
                false
            }
        } else {
            false
        };
        let non_determinism_return = if abort_signaled {
            debug!("BATCH[{batch_id}] all proof requests have been served from cache, skipping simulation");
            let (sender, receiver) = crossbeam_channel::bounded(1);
            sender
                .send(non_determinism_source)
                .expect("cached non-determinism return channel closed");
            receiver
        } else {
            self.spawn_simulation_workers(
                batch_id,
                binary_holder,
                non_determinism_source,
                &work_results_sender,
                &abort,
            )
        };
        let partial_tree_allocator_requests = (!proving
            && request_partial_trees
            && self.backend.persists_memory_partial_trees(profile))
        .then(|| {
            let (requests, keys) = unbounded();
            let free_allocators = self.free_allocators_receiver.clone();
            let results = work_results_sender.clone();
            spawn_abort_on_panic(format!("ab-partial-tree-allocator-{batch_id}"), move || {
                for (circuit_type, sequence_id) in keys {
                    let allocator = free_allocators
                        .recv()
                        .expect("partial-tree free allocator channel closed");
                    results
                        .send(WorkerResult::PartialTreeAllocator {
                            circuit_type,
                            sequence_id,
                            allocator,
                        })
                        .expect(
                            "worker results channel closed while sending a partial-tree allocator",
                        );
                }
            });
            requests
        });
        drop(work_results_sender);

        let mut request_context = RequestContext {
            proving,
            commitment_mode,
            profile,
            batch_id,
            binary_holder,
            external_challenges: external_challenges.as_ref(),
            partial_tree_allocator_requests,
            parked_commitments: BTreeMap::new(),
            proof_caps: &proof_caps,
            proof_partial_trees,
        };
        for sequence_id in trivial_unified_inits_and_teardowns {
            let data = InitsAndTeardownsData {
                circuit_type: binary_holder
                    .execution_kind
                    .unified_circuit()
                    .expect("trivial unified inits-and-teardowns belong to a unified execution"),
                sequence_id,
                inits_and_teardowns: None,
            };
            acc.unpaired_unified_inits_and_teardowns
                .insert(sequence_id, data);
        }
        match execution_kind {
            ExecutionKind::L1Wrap => {
                panic!("ExecutionKind::{execution_kind:?} requires prove_l1_wrap")
            }
            ExecutionKind::Unrolled => {
                let non_memory =
                    UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .iter()
                        .map(|t| t.get_family_idx());
                let memory =
                    UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .iter()
                        .map(|t| t.get_family_idx());
                for family_idx in non_memory.chain(memory) {
                    acc.circuit_families_memory_caps
                        .insert(family_idx, BTreeMap::new());
                    acc.circuit_families_proofs
                        .insert(family_idx, BTreeMap::new());
                }
            }
            ExecutionKind::Unified | ExecutionKind::Unified22 => {
                let family_idx = UnrolledCircuitType::Unified.get_family_idx();
                acc.circuit_families_memory_caps
                    .insert(family_idx, BTreeMap::new());
                acc.circuit_families_proofs
                    .insert(family_idx, BTreeMap::new());
            }
        }

        for work_result in work_results_receiver {
            let work_requests =
                acc.handle_work_result(self, cache, work_result, &mut request_context);
            dispatch_backend_requests(
                self,
                &requests_served_from_cache,
                work_requests,
                &work_requests_sender,
                &mut acc.pending_requests_count,
                &mut sent_requests_count,
            );
            if request_context.parked_commitments.is_empty() {
                maybe_close_request_sender_after_progress::<B>(
                    cache,
                    &mut work_requests_sender,
                    sent_requests_count,
                    &mut abort_signaled,
                    &mut acc.simulation_result,
                    &acc.uninitialized_tracing_data,
                    &acc.unpaired_unified_inits_and_teardowns,
                    &acc.unpaired_unified_tracing_data,
                    &abort,
                    proving,
                    batch_id,
                );
                if work_requests_sender.is_none() {
                    request_context.partial_tree_allocator_requests = None;
                }
            }
        }

        assert!(request_context.parked_commitments.is_empty());
        assert_eq!(acc.pending_requests_count, 0);
        if abort_signaled {
            std::mem::take(&mut acc.uninitialized_tracing_data)
                .into_values()
                .for_each(|data| {
                    self.free_tracing_data(data.tracing_data);
                });
            std::mem::take(&mut acc.unpaired_unified_inits_and_teardowns)
                .into_values()
                .for_each(|data| {
                    if let Some(inits_and_teardowns) = data.inits_and_teardowns {
                        self.free_inits_and_teardowns(inits_and_teardowns);
                    }
                });
            std::mem::take(&mut acc.unpaired_unified_tracing_data)
                .into_values()
                .for_each(|data| {
                    self.free_tracing_data(data.tracing_data);
                });
        } else {
            assert!(acc.uninitialized_tracing_data.is_empty());
            assert!(acc.unpaired_unified_inits_and_teardowns.is_empty());
            assert!(acc.unpaired_unified_tracing_data.is_empty());
        }
        if let Some(cache) = cache.as_mut() {
            if proving {
                assert!(cache.is_empty())
            } else {
                cache.total_requests_count = sent_requests_count;
                cache.trivial_unified_inits_and_teardowns_count =
                    acc.trivial_unified_inits_and_teardowns_count;
                cache.simulation_result = acc.simulation_result.clone();
            }
        }
        for trees in request_context.proof_partial_trees.into_values() {
            self.free_buffer(Some(trees.nodes));
        }
        let non_determinism_source = non_determinism_return
            .recv()
            .expect("simulation did not return its non-determinism source");
        (
            assemble_result(acc, proving, pow_challenge, binary_key, profile),
            non_determinism_source,
        )
    }

    pub(super) fn commit_memory_inner<ND: NonDeterminismCSRSource + Send + 'static>(
        &self,
        cache: &mut Option<TraceCache<B::Allocator>>,
        batch_id: u64,
        handle: BinaryHandle,
        non_determinism_source: ND,
        profile: ProofProfile,
        request_partial_trees: bool,
    ) -> (
        CommitMemoryResult,
        ND,
        MemoryPartialTreesByInstance<B::Allocator>,
    ) {
        let binary_key = handle.0;
        info!(
            "BATCH[{batch_id}] PROVER producing memory commitments for binary with key {binary_key:?}"
        );
        let timer = Instant::now();
        let (result, non_determinism_source) = self.get_result(
            false,
            request_partial_trees,
            cache,
            batch_id,
            binary_key,
            non_determinism_source,
            0,
            None,
            BTreeMap::new(),
            BTreeMap::new(),
            profile,
        );
        let (mut result, memory_partial_trees) = result.into_memory_commitment_result();
        result.binary_handle = handle;
        let elapsed = timer.elapsed().as_secs_f64();
        info!(
            "BATCH[{batch_id}] PROVER produced memory commitments for binary with key {binary_key:?} in {elapsed:.3}s"
        );
        (result, non_determinism_source, memory_partial_trees)
    }

    pub(super) fn prove_inner<ND: NonDeterminismCSRSource + Send + 'static>(
        &self,
        cache: &mut Option<TraceCache<B::Allocator>>,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: ND,
        pow_challenge: u64,
        external_challenges: GKRExternalChallenges<BF, E4>,
        proof_caps: BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
        proof_partial_trees: BTreeMap<(CircuitType, usize), MemoryPartialTrees<B::Allocator>>,
        profile: ProofProfile,
    ) -> ProveResult {
        info!("BATCH[{batch_id}] PROVER producing proofs for binary with key {binary_key:?}");
        let timer = Instant::now();
        let (result, _) = self.get_result(
            true,
            false,
            cache,
            batch_id,
            binary_key,
            non_determinism_source,
            pow_challenge,
            Some(external_challenges),
            proof_caps,
            proof_partial_trees,
            profile,
        );
        let result = result.into_proof_result();
        let elapsed = timer.elapsed().as_secs_f64();
        info!(
            "BATCH[{batch_id}] PROVER produced proofs for binary with key {binary_key:?} in {elapsed:.3}s"
        );
        result
    }
}

/// Consume the collected [`ResultAccumulator`] and fold it into the final
/// [`ProveResult`] / [`CommitMemoryResult`], flattening the per-family and
/// per-delegation `BTreeMap`s into the sequence-ordered `Vec`s the callers
/// expect.
fn assemble_result<A: fft::GoodAllocator>(
    acc: ResultAccumulator<A>,
    proving: bool,
    pow_challenge: u64,
    binary_key: usize,
    profile: ProofProfile,
) -> ExecutionProverResult<A> {
    let ResultAccumulator {
        trivial_unified_inits_and_teardowns_count,
        inits_and_teardowns_top_bits,
        simulation_result,
        circuit_families_memory_caps,
        inits_and_teardowns_memory_caps,
        delegation_circuits_memory_caps,
        memory_partial_trees,
        circuit_families_proofs,
        inits_and_teardowns_proofs,
        delegation_circuits_proofs,
        ..
    } = acc;
    let SimulationResult {
        final_register_values,
        final_pc,
        final_timestamp,
    } = simulation_result.expect("simulation result must be present before get_result returns");
    if proving {
        let circuit_families_proofs = circuit_families_proofs
            .into_iter()
            .map(|(i, v)| (i, v.into_values().collect_vec()))
            .collect();
        let inits_and_teardowns_proofs = inits_and_teardowns_proofs.into_values().collect_vec();
        let delegation_circuits_proofs = delegation_circuits_proofs
            .into_iter()
            .map(|(i, v)| (i, v.into_values().collect_vec()))
            .collect();
        let circuit_families_proofs: BTreeMap<_, Vec<_>> = circuit_families_proofs;
        // Unified mode: real inits-and-teardowns circuits are the trailing
        // ones; everything before `trivial_unified_inits_and_teardowns_count`
        // is a dummy marker.
        let num_unified_it_circuits = circuit_families_proofs
            .get(&UnrolledCircuitType::Unified.get_family_idx())
            .map(|unified_proofs| {
                // Trivial-marker sequence_ids are a subset of the Unified
                // proofs collected above (every sequence_id, trivial or
                // real, goes through the same WorkResult::Proof insert),
                // so this subtraction can never underflow on valid state.
                assert!(
                    unified_proofs.len() >= trivial_unified_inits_and_teardowns_count,
                    "unified proof count {} below trivial i&t count {}",
                    unified_proofs.len(),
                    trivial_unified_inits_and_teardowns_count
                );
                (unified_proofs.len() - trivial_unified_inits_and_teardowns_count) as u32
            });
        let result = ProveResult {
            register_final_values: final_register_values,
            final_pc,
            final_timestamp,
            circuit_families_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs: delegation_circuits_proofs,
            pow_challenge,
            num_unified_it_circuits,
        };
        ExecutionProverResult::Prove(Box::new(result))
    } else {
        let circuit_families_memory_caps = circuit_families_memory_caps
            .into_iter()
            .map(|(i, v)| (i, v.into_values().collect_vec()))
            .collect();
        let inits_and_teardowns_memory_caps =
            inits_and_teardowns_memory_caps.into_values().collect_vec();
        let delegation_circuits_memory_caps = delegation_circuits_memory_caps
            .into_iter()
            .map(|(i, v)| (i, v.into_values().collect_vec()))
            .collect();
        let result = CommitMemoryResult {
            profile,
            final_register_values,
            final_pc,
            final_timestamp,
            circuit_families_memory_caps,
            inits_and_teardowns_memory_caps,
            delegation_circuits_memory_caps,
            num_trivial_unified_circuits: trivial_unified_inits_and_teardowns_count,
            inits_and_teardowns_top_bits,
            binary_handle: BinaryHandle(binary_key),
        };
        ExecutionProverResult::CommitMemory(Box::new(result), memory_partial_trees)
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::test_support::TestBackend;

    #[test]
    #[should_panic(
        expected = "MergedMemoryAndWitness does not support delegation calls or circuits"
    )]
    fn l1_profile_rejects_delegation_requests() {
        let mut prover = ExecutionProver::<TestBackend>::new();
        let program = vec![0x0001_2083, 0xffdf_f06f];
        let profile = ProofProfile::CompressionFinal;
        let kind = ExecutionKind::Unified22;
        let handle = prover.add_binary_variants(
            program.clone(),
            program,
            &[(kind, MachineType::Reduced, &[profile])],
            Some(32),
        )[0];
        prover.finalize_setup();
        let proof_caps = BTreeMap::new();
        let mut context = RequestContext {
            proving: false,
            commitment_mode: crate::config::execution_commitment_mode(
                kind,
                profile,
                prover.configuration.soundness_mode,
                |circuit| prover.binary_holders[&handle.0].compiled_circuit(circuit),
            ),
            profile,
            batch_id: 1,
            binary_holder: &prover.binary_holders[&handle.0],
            external_challenges: None,
            partial_tree_allocator_requests: None,
            parked_commitments: BTreeMap::new(),
            proof_caps: &proof_caps,
            proof_partial_trees: Default::default(),
        };
        let _ = context.build_work_request(
            &prover,
            Some(InitsAndTeardownsData {
                circuit_type: CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
                sequence_id: 0,
                inits_and_teardowns: None,
            }),
            None,
        );
    }
}
