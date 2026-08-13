use super::*;

type ScheduledProof = crate::upstream::GKRProof<BF, E4, crate::upstream::DefaultTreeConstructor>;

pub(super) struct RequestContext<'a> {
    pub(super) proving: bool,
    pub(super) batch_id: u64,
    pub(super) binary_holder: &'a BinaryHolder,
    pub(super) external_challenges: Option<&'a GKRExternalChallenges<BF, E4>>,
    pub(super) proof_caps: &'a BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
}

impl<'a> RequestContext<'a> {
    pub(super) fn build_gpu_work_request(
        &self,
        prover: &ExecutionProver,
        inits_and_teardowns: Option<InitsAndTeardownsData>,
        tracing_data: Option<TracingData<A>>,
    ) -> GpuWorkRequest<A> {
        let mut circuit_type_value = None;
        let mut sequence_id_value = None;
        let inits_and_teardowns = if let Some(inits_and_teardowns) = inits_and_teardowns {
            let InitsAndTeardownsData {
                circuit_type,
                sequence_id,
                inits_and_teardowns,
            } = inits_and_teardowns;
            circuit_type_value = Some(circuit_type);
            sequence_id_value = Some(sequence_id);
            inits_and_teardowns
        } else {
            None
        };
        let tracing_data = if let Some(tracing_data) = tracing_data {
            let TracingData {
                circuit_type,
                sequence_id,
                tracing_data,
                ..
            } = tracing_data;
            assert_eq!(
                circuit_type_value.get_or_insert(circuit_type),
                &circuit_type
            );
            assert_eq!(sequence_id_value.get_or_insert(sequence_id), &sequence_id);
            Some(tracing_data)
        } else {
            None
        };
        let circuit_type = circuit_type_value.expect(
            "get_gpu_work_request needs at least one of inits_and_teardowns or tracing_data",
        );
        let sequence_id = sequence_id_value.expect(
            "get_gpu_work_request needs at least one of inits_and_teardowns or tracing_data",
        );
        let precomputations = match circuit_type {
            CircuitType::Delegation(_)
            | CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                prover.common_precomputations[&circuit_type].clone()
            }
            CircuitType::Unrolled(circuit_type) => {
                self.binary_holder.precomputations[&circuit_type].clone()
            }
        };
        if self.proving {
            let memory_caps = self
                .proof_caps
                .get(&(circuit_type, sequence_id))
                .expect("missing memory caps for proof request")
                .clone();
            let request = ProofRequest {
                batch_id: self.batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                external_challenges: *self
                    .external_challenges
                    .expect("proof request construction requires external challenges"),
                memory_caps,
                security_level: prover.configuration.security_level,
            };
            GpuWorkRequest::Proof(request)
        } else {
            let request = MemoryCommitmentRequest {
                batch_id: self.batch_id,
                circuit_type,
                sequence_id,
                precomputations,
                inits_and_teardowns,
                tracing_data,
                security_level: prover.configuration.security_level,
            };
            GpuWorkRequest::MemoryCommitment(request)
        }
    }
}

fn enqueue_ready_tracing_data(
    prover: &ExecutionProver,
    request_context: &RequestContext<'_>,
    data: TracingData<A>,
    gpu_work_requests: &mut VecDeque<GpuWorkRequest<A>>,
    unpaired_unified_inits_and_teardowns: &mut BTreeMap<usize, InitsAndTeardownsData>,
    unpaired_unified_tracing_data: &mut BTreeMap<usize, TracingData<A>>,
) {
    match data.circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            panic!("tracing data can not have the inits and teardowns circuit_type")
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
            let sequence_id = data.sequence_id;
            assert!(!unpaired_unified_tracing_data.contains_key(&sequence_id));
            if let Some(inits_and_teardowns) =
                unpaired_unified_inits_and_teardowns.remove(&sequence_id)
            {
                let request = request_context.build_gpu_work_request(
                    prover,
                    Some(inits_and_teardowns),
                    Some(data),
                );
                gpu_work_requests.push_back(request);
            } else {
                assert!(unpaired_unified_tracing_data
                    .insert(sequence_id, data)
                    .is_none());
            }
        }
        _ => {
            let request = request_context.build_gpu_work_request(prover, None, Some(data));
            gpu_work_requests.push_back(request);
        }
    }
}

/// Accumulated state threaded through the work-result loop in
/// [`ExecutionProver::get_result`]. Bundling these fields keeps
/// [`ResultAccumulator::handle_work_result`] and its
/// [`ResultAccumulator::consume_gpu_work_result`] helper down to their genuine
/// per-call inputs, and lets the final assembly read the collected proofs/caps
/// straight off the struct.
#[derive(Default)]
pub(super) struct ResultAccumulator {
    pub(super) pending_requests_count: usize,
    pub(super) trivial_unified_inits_and_teardowns_count: usize,
    pub(super) processed_snapshots: BTreeSet<usize>,
    pub(super) uninitialized_tracing_data: BTreeMap<(CircuitType, usize), TracingData<A>>,
    pub(super) uninitialized_tracing_data_key_by_snapshot_index:
        BTreeMap<usize, BTreeSet<(CircuitType, usize)>>,
    pub(super) unpaired_unified_inits_and_teardowns: BTreeMap<usize, InitsAndTeardownsData>,
    pub(super) unpaired_unified_tracing_data: BTreeMap<usize, TracingData<A>>,
    /// Unified mode: the i&t address windows each real i&t-carrying instance was
    /// assigned. Trivial (leading) instances are absent.
    pub(super) unified_inits_and_teardowns_top_bits: BTreeMap<usize, Vec<u32>>,
    pub(super) simulation_result: Option<SimulationResult>,
    pub(super) circuit_families_memory_caps:
        BTreeMap<u8, BTreeMap<usize, Vec<MerkleTreeCapVarLength>>>,
    pub(super) inits_and_teardowns_memory_caps: BTreeMap<usize, Vec<MerkleTreeCapVarLength>>,
    pub(super) delegation_circuits_memory_caps:
        BTreeMap<u32, BTreeMap<usize, Vec<MerkleTreeCapVarLength>>>,
    pub(super) circuit_families_proofs: BTreeMap<u8, BTreeMap<usize, ScheduledProof>>,
    pub(super) inits_and_teardowns_proofs: BTreeMap<usize, ScheduledProof>,
    pub(super) delegation_circuits_proofs: BTreeMap<u32, BTreeMap<usize, ScheduledProof>>,
}

impl ResultAccumulator {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn handle_work_result(
        &mut self,
        prover: &ExecutionProver,
        cache: &mut Option<TraceCache>,
        work_result: WorkerResult<A>,
        request_context: &RequestContext<'_>,
    ) -> VecDeque<GpuWorkRequest<A>> {
        let mut gpu_work_requests = VecDeque::new();
        match work_result {
            WorkerResult::SnapshotProduced => {
                if !request_context.proving {
                    if let Some(cache) = cache.as_mut() {
                        prover.trim_cache(cache)
                    }
                }
            }
            WorkerResult::InitsAndTeardownsData(data) => match data.circuit_type {
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    let request = request_context.build_gpu_work_request(prover, Some(data), None);
                    gpu_work_requests.push_back(request);
                }
                CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
                    let sequence_id = data.sequence_id;
                    if sequence_id < self.trivial_unified_inits_and_teardowns_count {
                        assert!(data.inits_and_teardowns.is_none());
                    }
                    if let Some(host) = data.inits_and_teardowns.as_ref() {
                        self.unified_inits_and_teardowns_top_bits
                            .insert(sequence_id, host.top_bits.clone());
                    }
                    if !request_context.proving
                        || cache.is_none()
                        || sequence_id >= self.trivial_unified_inits_and_teardowns_count
                    {
                        assert!(!self
                            .unpaired_unified_inits_and_teardowns
                            .contains_key(&sequence_id));
                        if sequence_id >= self.trivial_unified_inits_and_teardowns_count {
                            if request_context.proving && cache.is_some() {
                                assert!(data.inits_and_teardowns.is_some())
                            } else if data.inits_and_teardowns.is_none() {
                                self.trivial_unified_inits_and_teardowns_count = sequence_id + 1;
                            }
                        }
                        if let Some(tracing_data) =
                            self.unpaired_unified_tracing_data.remove(&sequence_id)
                        {
                            let request = request_context.build_gpu_work_request(
                                prover,
                                Some(data),
                                Some(tracing_data),
                            );
                            gpu_work_requests.push_back(request);
                        } else {
                            assert!(self
                                .unpaired_unified_inits_and_teardowns
                                .insert(sequence_id, data)
                                .is_none());
                        }
                    }
                }
                _ => panic!("unexpected circuit type for inits and teardowns data"),
            },
            WorkerResult::TracingData(data) => {
                if data
                    .participating_snapshot_indexes
                    .is_subset(&self.processed_snapshots)
                {
                    enqueue_ready_tracing_data(
                        prover,
                        request_context,
                        data,
                        &mut gpu_work_requests,
                        &mut self.unpaired_unified_inits_and_teardowns,
                        &mut self.unpaired_unified_tracing_data,
                    );
                } else {
                    let key = (data.circuit_type, data.sequence_id);
                    for snapshot_index in data.participating_snapshot_indexes.iter().copied() {
                        let entry = self
                            .uninitialized_tracing_data_key_by_snapshot_index
                            .entry(snapshot_index)
                            .or_default();
                        assert!(!entry.contains(&key));
                        entry.insert(key);
                    }
                    assert!(self.uninitialized_tracing_data.insert(key, data).is_none());
                }
            }
            WorkerResult::SimulationResult(result) => {
                self.simulation_result = Some(result);
            }
            WorkerResult::SnapshotReplayed(sequence_id) => {
                assert!(self.processed_snapshots.insert(sequence_id));
                if let Some(keys) = self
                    .uninitialized_tracing_data_key_by_snapshot_index
                    .get_mut(&sequence_id)
                {
                    for key in keys.clone().into_iter() {
                        if self
                            .uninitialized_tracing_data
                            .get(&key)
                            .unwrap()
                            .participating_snapshot_indexes
                            .is_subset(&self.processed_snapshots)
                        {
                            keys.remove(&key);
                            let data = self.uninitialized_tracing_data.remove(&key).unwrap();
                            enqueue_ready_tracing_data(
                                prover,
                                request_context,
                                data,
                                &mut gpu_work_requests,
                                &mut self.unpaired_unified_inits_and_teardowns,
                                &mut self.unpaired_unified_tracing_data,
                            );
                        }
                    }
                }
            }
            WorkerResult::GpuWorkResult(result) => {
                assert_ne!(self.pending_requests_count, 0);
                self.pending_requests_count -= 1;
                self.consume_gpu_work_result(prover, cache, request_context.proving, result);
            }
        }

        gpu_work_requests
    }

    fn consume_gpu_work_result(
        &mut self,
        prover: &ExecutionProver,
        cache: &mut Option<TraceCache>,
        proving: bool,
        result: GpuWorkResult<A>,
    ) {
        match result {
            GpuWorkResult::MemoryCommitment(commitment) => {
                assert!(!proving);
                let MemoryCommitmentResult {
                    batch_id,
                    circuit_type,
                    sequence_id,
                    inits_and_teardowns,
                    tracing_data,
                    merkle_tree_caps,
                } = commitment;
                trace!(
                    "BATCH[{batch_id}] PROVER received memory commitment for circuit {circuit_type:?}[{sequence_id}]"
                );
                if let Some(cache) = cache.as_mut() {
                    let cache_entry = TraceCacheEntry {
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                        tracing_data,
                    };
                    cache.push_back(cache_entry);
                    if self.simulation_result.is_none() {
                        prover.trim_cache(cache);
                    }
                } else {
                    prover.free_traces(inits_and_teardowns, tracing_data)
                }
                let caps: &mut BTreeMap<usize, Vec<MerkleTreeCapVarLength>> = match circuit_type {
                    CircuitType::Delegation(circuit_type) => self
                        .delegation_circuits_memory_caps
                        .entry(circuit_type as u32)
                        .or_default(),
                    CircuitType::Unrolled(circuit_type) => match circuit_type {
                        UnrolledCircuitType::InitsAndTeardowns => {
                            &mut self.inits_and_teardowns_memory_caps
                        }
                        _ => self
                            .circuit_families_memory_caps
                            .get_mut(&circuit_type.get_family_idx())
                            .unwrap(),
                    },
                };
                assert!(caps.insert(sequence_id, merkle_tree_caps).is_none());
            }
            GpuWorkResult::Proof(proof) => {
                assert!(proving);
                let ProofResult {
                    batch_id,
                    circuit_type,
                    sequence_id,
                    inits_and_teardowns,
                    tracing_data,
                    proof,
                } = proof;
                trace!(
                    "BATCH[{batch_id}] PROVER received proof for circuit {circuit_type:?}[{sequence_id}]"
                );
                prover.free_traces(inits_and_teardowns, tracing_data);
                match circuit_type {
                    CircuitType::Delegation(circuit_type) => {
                        assert!(self
                            .delegation_circuits_proofs
                            .entry(circuit_type as u32)
                            .or_default()
                            .insert(sequence_id, proof)
                            .is_none())
                    }
                    CircuitType::Unrolled(circuit_type) => match circuit_type {
                        UnrolledCircuitType::InitsAndTeardowns => {
                            assert!(self
                                .inits_and_teardowns_proofs
                                .insert(sequence_id, proof)
                                .is_none())
                        }
                        _ => assert!(self
                            .circuit_families_proofs
                            .get_mut(&circuit_type.get_family_idx())
                            .unwrap()
                            .insert(sequence_id, proof)
                            .is_none()),
                    },
                };
            }
        }
    }
}

pub(super) fn dispatch_gpu_requests(
    prover: &ExecutionProver,
    requests_served_from_cache: &BTreeSet<(CircuitType, usize)>,
    gpu_work_requests: VecDeque<GpuWorkRequest<A>>,
    gpu_work_requests_sender: &Option<Sender<GpuWorkRequest<A>>>,
    pending_requests_count: &mut usize,
    sent_requests_count: &mut usize,
) {
    for request in gpu_work_requests {
        let key = (request.circuit_type(), request.sequence_id());
        if requests_served_from_cache.contains(&key) {
            match request {
                GpuWorkRequest::Proof(request) => {
                    let ProofRequest {
                        batch_id,
                        circuit_type,
                        sequence_id,
                        inits_and_teardowns,
                        tracing_data,
                        ..
                    } = request;
                    trace!(
                        "BATCH[{batch_id}] PROVER skipping cached proof request for circuit {circuit_type:?}[{sequence_id}]"
                    );
                    prover.free_traces(inits_and_teardowns, tracing_data);
                }
                _ => panic!("only proof requests are cached"),
            }
            continue;
        }
        gpu_work_requests_sender
            .as_ref()
            .unwrap()
            .send(request)
            .unwrap();
        *pending_requests_count += 1;
        *sent_requests_count += 1;
    }
}

pub(super) fn maybe_close_gpu_sender_after_progress(
    cache: &mut Option<TraceCache>,
    gpu_work_requests_sender: &mut Option<Sender<GpuWorkRequest<A>>>,
    sent_requests_count: usize,
    abort_signaled: &mut bool,
    simulation_result: &mut Option<SimulationResult>,
    uninitialized_tracing_data: &BTreeMap<(CircuitType, usize), TracingData<A>>,
    unpaired_unified_inits_and_teardowns: &BTreeMap<usize, InitsAndTeardownsData>,
    unpaired_unified_tracing_data: &BTreeMap<usize, TracingData<A>>,
    abort: &Arc<AtomicBool>,
    proving: bool,
    batch_id: u64,
) {
    if simulation_result.is_some()
        && uninitialized_tracing_data.is_empty()
        && unpaired_unified_inits_and_teardowns.is_empty()
        && unpaired_unified_tracing_data.is_empty()
    {
        *gpu_work_requests_sender = None;
    }
    if let Some(cache) = cache.as_mut() {
        if proving
            && !*abort_signaled
            && gpu_work_requests_sender.is_some()
            && cache.total_requests_count == sent_requests_count
        {
            debug!(
                "BATCH[{batch_id}] PROVER all remaining proof requests have been served from cache, signaling abort of simulation"
            );
            *gpu_work_requests_sender = None;
            abort.store(true, std::sync::atomic::Ordering::Relaxed);
            *simulation_result = cache.simulation_result.clone();
            *abort_signaled = true;
        }
    }
}
