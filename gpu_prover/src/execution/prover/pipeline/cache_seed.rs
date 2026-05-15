use super::*;

pub(super) struct CacheSeedOutcome {
    pub(super) pending_requests_count: usize,
    pub(super) sent_requests_count: usize,
    pub(super) requests_served_from_cache: BTreeSet<(CircuitType, usize)>,
    pub(super) trivial_unified_inits_and_teardowns_count: usize,
    pub(super) trivial_unified_inits_and_teardowns: BTreeSet<usize>,
}

pub(super) fn seed_from_cache(
    prover: &ExecutionProver,
    binary_holder: &BinaryHolder,
    proving: bool,
    cache: &mut Option<TraceCache>,
    batch_id: u64,
    external_challenges: Option<&GKRExternalChallenges<BF, E4>>,
    proof_caps: &BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
    gpu_work_requests_sender: &Sender<GpuWorkRequest<A>>,
) -> CacheSeedOutcome {
    let mut pending_requests_count = 0;
    let mut sent_requests_count = 0;
    let mut requests_served_from_cache = BTreeSet::new();
    let mut trivial_unified_inits_and_teardowns_count = 0;
    let mut trivial_unified_inits_and_teardowns = BTreeSet::new();

    if let Some(cache) = cache.as_mut() {
        trivial_unified_inits_and_teardowns_count = cache.trivial_unified_inits_and_teardowns_count;
        for i in 0..trivial_unified_inits_and_teardowns_count {
            trivial_unified_inits_and_teardowns.insert(i);
        }
        for entry in cache.entries.drain(..) {
            let TraceCacheEntry {
                circuit_type,
                sequence_id,
                inits_and_teardowns,
                tracing_data,
            } = entry;
            if matches!(
                circuit_type,
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
            ) && sequence_id < trivial_unified_inits_and_teardowns_count
            {
                assert!(trivial_unified_inits_and_teardowns.remove(&sequence_id));
            }
            let precomputations = match circuit_type {
                CircuitType::Delegation(_)
                | CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    prover.common_precomputations[&circuit_type].clone()
                }
                CircuitType::Unrolled(circuit_type) => {
                    binary_holder.precomputations[&circuit_type].clone()
                }
            };
            let memory_caps = proof_caps
                .get(&(circuit_type, sequence_id))
                .expect("missing memory caps for proof request (cache path)")
                .clone();
            let request = ProofRequest {
                batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                external_challenges: external_challenges
                    .expect("proof cache seeding requires external challenges")
                    .clone(),
                memory_caps,
                security_level: prover.configuration.security_level,
            };
            let request = GpuWorkRequest::Proof(request);
            gpu_work_requests_sender
                .send(request)
                .expect("ExecutionProver GPU-work channel closed before proof dispatch");
            pending_requests_count += 1;
            sent_requests_count += 1;
            requests_served_from_cache.insert((circuit_type, sequence_id));
        }
    }

    if !proving {
        assert_eq!(pending_requests_count, 0);
        assert_eq!(sent_requests_count, 0);
        assert!(requests_served_from_cache.is_empty());
    }

    CacheSeedOutcome {
        pending_requests_count,
        sent_requests_count,
        requests_served_from_cache,
        trivial_unified_inits_and_teardowns_count,
        trivial_unified_inits_and_teardowns,
    }
}
