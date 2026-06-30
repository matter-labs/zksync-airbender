use super::*;

impl ExecutionProver {
    fn derive_proof_artifacts(
        &self,
        binary_key: usize,
        memory_commitment: &CommitMemoryResult,
    ) -> (
        u64,
        GKRExternalChallenges<BF, E4>,
        BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>>,
    ) {
        let CommitMemoryResult {
            final_register_values,
            final_pc,
            final_timestamp,
            circuit_families_memory_caps,
            inits_and_teardowns_memory_caps,
            delegation_circuits_memory_caps,
            binary_handle: _,
        } = memory_commitment;
        let all_challenges_seed = fs_transform_for_permutation_argument(
            final_register_values,
            *final_pc,
            *final_timestamp,
            &circuit_families_memory_caps
                .iter()
                .map(|(i, v)| (*i as u32, v.clone()))
                .collect_vec(),
            inits_and_teardowns_memory_caps,
            &delegation_circuits_memory_caps
                .iter()
                .map(|(i, v)| (*i, v.clone()))
                .collect_vec(),
        );
        let pow_challenge = if MEMORY_DELEGATION_POW_BITS == 0 {
            0
        } else {
            Transcript::search_pow(
                &all_challenges_seed,
                MEMORY_DELEGATION_POW_BITS as u32,
                &self.worker,
            )
            .1
        };
        let external_challenges = GKRExternalChallenges::<BF, E4>::draw_from_transcript_seed(
            all_challenges_seed,
            MEMORY_DELEGATION_POW_BITS,
            pow_challenge,
        );
        let machine_type = self.binary_holders[&binary_key].machine_type;
        let mut proof_caps: BTreeMap<(CircuitType, usize), Vec<MerkleTreeCapVarLength>> =
            BTreeMap::new();
        for (family_idx, per_seq) in circuit_families_memory_caps.iter() {
            let circuit_type = unrolled_circuit_type_from_family_idx(*family_idx, machine_type);
            for (sequence_id, caps) in per_seq.iter().enumerate() {
                proof_caps.insert(
                    (CircuitType::Unrolled(circuit_type), sequence_id),
                    caps.clone(),
                );
            }
        }
        for (sequence_id, caps) in inits_and_teardowns_memory_caps.iter().enumerate() {
            proof_caps.insert(
                (
                    CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
                    sequence_id,
                ),
                caps.clone(),
            );
        }
        for (delegation_type, per_seq) in delegation_circuits_memory_caps.iter() {
            let delegation_type = DelegationCircuitType::try_from(*delegation_type as u16)
                .expect("delegation memory-cap map must only contain supported delegation ids");
            for (sequence_id, caps) in per_seq.iter().enumerate() {
                proof_caps.insert(
                    (CircuitType::Delegation(delegation_type), sequence_id),
                    caps.clone(),
                );
            }
        }
        (pow_challenge, external_challenges, proof_caps)
    }

    pub fn commit_memory(
        &self,
        batch_id: u64,
        handle: &BinaryHandle,
        non_determinism_source: impl NonDeterminismCSRSource + Send + 'static,
    ) -> CommitMemoryResult {
        let non_determinism_source = Arc::new(Mutex::new(Some(non_determinism_source)));
        self.commit_memory_inner(&mut None, batch_id, *handle, non_determinism_source)
    }

    pub fn prove(
        &self,
        batch_id: u64,
        commit_ticket: CommitMemoryResult,
        non_determinism_source: impl NonDeterminismCSRSource + Send + 'static,
    ) -> ProveResult {
        let binary_key = commit_ticket.binary_handle.0;
        let (pow_challenge, external_challenges, proof_caps) =
            self.derive_proof_artifacts(binary_key, &commit_ticket);
        let non_determinism_source = Arc::new(Mutex::new(Some(non_determinism_source)));
        let mut cache = None;
        self.prove_inner(
            &mut cache,
            batch_id,
            binary_key,
            non_determinism_source,
            pow_challenge,
            external_challenges,
            proof_caps,
        )
    }

    pub fn commit_memory_and_prove(
        &self,
        batch_id: u64,
        handle: &BinaryHandle,
        non_determinism_source: impl NonDeterminismCSRSource + Send + 'static,
    ) -> ProveResult {
        let binary_key = handle.0;
        let nd_wrapper = NonDeterminismWrapper::new(non_determinism_source);
        let non_determinism_source = Arc::new(Mutex::new(Some(nd_wrapper)));
        let mut cache = Some(TraceCache::new());
        let timer = Instant::now();
        let memory_commitment = self.commit_memory_inner(
            &mut cache,
            batch_id,
            *handle,
            non_determinism_source.clone(),
        );
        let non_determinism_values = Arc::into_inner(non_determinism_source)
            .expect("non_determinism_source Arc still has other strong refs after commit_memory")
            .into_inner()
            .expect("non_determinism_source Mutex was poisoned")
            .expect("commit_memory consumed the non_determinism_source")
            .into_values();
        let non_determinism_source = Arc::new(Mutex::new(Some(QuasiUARTSource::new_with_reads(
            non_determinism_values,
        ))));
        let (pow_challenge, external_challenges, proof_caps) =
            self.derive_proof_artifacts(binary_key, &memory_commitment);
        let final_register_values = memory_commitment.final_register_values;
        let final_pc = memory_commitment.final_pc;
        let final_timestamp = memory_commitment.final_timestamp;
        let prove_result = self.prove_inner(
            &mut cache,
            batch_id,
            binary_key,
            non_determinism_source,
            pow_challenge,
            external_challenges,
            proof_caps,
        );
        assert_eq!(prove_result.register_final_values, final_register_values);
        assert_eq!(prove_result.final_pc, final_pc);
        assert_eq!(prove_result.final_timestamp, final_timestamp);
        let elapsed = timer.elapsed().as_secs_f64();
        info!(
            "BATCH[{batch_id}] PROVER committed to memory and produced proofs for binary with key {binary_key:?} in {elapsed:.3}s"
        );
        prove_result
    }
}

fn fs_transform_for_permutation_argument(
    final_register_values: &[FinalRegisterValue; 32],
    final_pc: u32,
    final_timestamp: TimestampScalar,
    circuit_families_memory_caps: &[(u32, Vec<Vec<MerkleTreeCapVarLength>>)],
    inits_and_teardowns_memory_caps: &[Vec<MerkleTreeCapVarLength>],
    delegation_circuits_memory_caps: &[(u32, Vec<Vec<MerkleTreeCapVarLength>>)],
) -> crate::upstream::Seed {
    let circuit_families_memory_caps = circuit_families_memory_caps
        .iter()
        .map(|(family, per_sequence_caps)| {
            (
                *family,
                per_sequence_caps
                    .iter()
                    .flat_map(|caps| caps.iter().cloned())
                    .collect_vec(),
            )
        })
        .collect_vec();
    let inits_and_teardowns_memory_caps = inits_and_teardowns_memory_caps
        .iter()
        .flat_map(|caps| caps.iter().cloned())
        .collect_vec();
    let delegation_circuits_memory_caps = delegation_circuits_memory_caps
        .iter()
        .map(|(delegation_type, per_sequence_caps)| {
            (
                *delegation_type,
                per_sequence_caps
                    .iter()
                    .flat_map(|caps| caps.iter().cloned())
                    .collect_vec(),
            )
        })
        .collect_vec();
    crate::upstream::fs_transform_for_permutation_argument::<true>(
        final_register_values,
        final_pc,
        final_timestamp,
        &circuit_families_memory_caps,
        &inits_and_teardowns_memory_caps,
        &delegation_circuits_memory_caps,
    )
}

fn unrolled_circuit_type_from_family_idx(
    family_idx: u8,
    machine_type: MachineType,
) -> UnrolledCircuitType {
    for ct in UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine_type) {
        if ct.get_family_idx() == family_idx {
            return UnrolledCircuitType::Memory(*ct);
        }
    }
    for ct in UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine_type) {
        if ct.get_family_idx() == family_idx {
            return UnrolledCircuitType::NonMemory(*ct);
        }
    }
    if family_idx == UnrolledCircuitType::Unified.get_family_idx() {
        return UnrolledCircuitType::Unified;
    }
    panic!("unknown unrolled family idx {family_idx} for machine type {machine_type:?}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduced_machine_idx_maps_to_unified() {
        let ct = unrolled_circuit_type_from_family_idx(
            UnrolledCircuitType::Unified.get_family_idx(),
            MachineType::Reduced,
        );
        assert_eq!(ct, UnrolledCircuitType::Unified);
    }
}
