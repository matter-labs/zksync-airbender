use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Register the requested execution variants of one binary at initialization.
    /// Padding, instruction decoding and family projections are shared across variants.
    pub fn add_binary_variants(
        &mut self,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        variants: &[(ExecutionKind, MachineType, &[ProofProfile])],
        cycles_bound: Option<u32>,
    ) -> Vec<BinaryHandle> {
        assert!(
            self.host_pool_allocation.is_some(),
            "cannot register binary variants after finalizing setup"
        );
        assert!(
            !variants.is_empty(),
            "at least one binary variant is required"
        );
        let variants: Vec<_> = variants
            .iter()
            .map(|&(execution_kind, machine_type, profiles)| {
                assert!(
                    !profiles.is_empty(),
                    "add_binary needs at least one ProofProfile"
                );
                let mut profiles = profiles.to_vec();
                profiles.sort_unstable();
                profiles.dedup();
                if execution_kind.is_l1_wrap() {
                    assert_eq!(
                        machine_type,
                        MachineType::Reduced,
                        "ExecutionKind::{execution_kind:?} requires MachineType::Reduced"
                    );
                }
                if let Some(circuit) = execution_kind.unified_circuit() {
                    crate::config::assert_profiles_for_circuit(circuit, &profiles);
                } else {
                    for circuit in
                        crate::setup::circuit_types_for_variant(execution_kind, machine_type)
                    {
                        crate::config::assert_profiles_for_circuit(
                            CircuitType::Unrolled(circuit),
                            &profiles,
                        );
                    }
                }
                for profile in &profiles {
                    profile
                        .config_profile()
                        .assert_supports(self.configuration.soundness_mode);
                }
                (execution_kind, machine_type, profiles)
            })
            .collect();
        for (i, (kind, machine, _)) in variants.iter().enumerate() {
            assert!(
                !variants[..i]
                    .iter()
                    .any(|(k, m, _)| (k, m) == (kind, machine)),
                "duplicate binary variant"
            );
        }
        let decode_start = Instant::now();
        let machines = baby_bear::setup::preprocess_machines(&variants, &text_section);
        info!(
            "PROVER decoded and padded binary for {} variants on {} machines in {:?}",
            variants.len(),
            machines.len(),
            decode_start.elapsed()
        );
        let binary_image = Arc::new(binary_image.into_boxed_slice());
        let text_section = Arc::new(text_section.into_boxed_slice());
        let mut handles = Vec::with_capacity(variants.len());
        for (execution_kind, machine_type, profiles) in variants {
            let unified_circuit = execution_kind.unified_circuit();
            let key = self.next_binary_id;
            info!(
                "PROVER inserting binary with key {key:?} ({execution_kind:?}, {machine_type:?})"
            );
            let mut padded_binary_image = binary_image.to_vec();
            crate::upstream::pad_bytecode_for_proving_with_rom(
                &mut padded_binary_image,
                execution_kind.rom(),
            );
            let (
                instruction_tape,
                precomputations,
                l1_wrap_precomputations,
                (setup_time, preparation_time),
            ) = if execution_kind.is_l1_wrap() {
                let (instruction_tape, precomputations) = self.prepare_l1_wrap(
                    unified_circuit.unwrap(),
                    &padded_binary_image,
                    &text_section,
                    &profiles,
                );
                (
                    instruction_tape,
                    HashMap::new(),
                    Some(precomputations),
                    Default::default(),
                )
            } else {
                let (_, preprocessing, instruction_tape) = machines
                    .iter()
                    .find(|(machine, _, _)| *machine == machine_type)
                    .unwrap();
                let (precomputations, times) = self.prepare_riscv_families(
                    key,
                    execution_kind,
                    machine_type,
                    &padded_binary_image,
                    preprocessing,
                    &profiles,
                );
                (Arc::clone(instruction_tape), precomputations, None, times)
            };
            let start = Instant::now();
            // Common setup uses 0; each variant needs a distinct batch while
            // earlier setup requests can still be running in the backend.
            let setup_batch_id = u64::try_from(key)
                .unwrap()
                .checked_add(1)
                .expect("setup batch id overflow");
            let pending = request_setup_initialization(
                self.backend.as_ref(),
                setup_batch_id,
                precomputations
                    .iter()
                    .map(|(circuit_type, precomp)| {
                        (CircuitType::Unrolled(*circuit_type), precomp.clone())
                    })
                    .chain(
                        l1_wrap_precomputations
                            .iter()
                            .map(|precomp| (unified_circuit.unwrap(), precomp.clone())),
                    )
                    .collect(),
            );
            self.pending_setup_initializations.push(pending);
            info!("PROVER inserted binary with key {key:?}: CPU setup construction {setup_time:?}, backend preparation {preparation_time:?}, setup initialization request {:?}", start.elapsed());
            let holder = BinaryHolder {
                execution_kind,
                profiles,
                machine_type,
                binary_image: Arc::clone(&binary_image),
                text_section: Arc::clone(&text_section),
                cycles_bound,
                instruction_tape,
                jit_cache: Arc::new(Mutex::new(TypeMap::new())),
                precomputations,
                l1_wrap_precomputations,
            };
            assert!(self.binary_holders.insert(key, holder).is_none());
            self.next_binary_id += 1;
            handles.push(BinaryHandle(key));
        }
        handles
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::config::SoundnessMode;
    use crate::test_support::TestBackend;

    /// Every L1 profile under ethproofs is rejected before a binary is registered.
    #[test]
    fn ethproofs_l1_binary_is_rejected_before_registration() {
        let soundness_mode = SoundnessMode::EthproofsSoundnessCalc;
        let mut prover = ExecutionProver::<TestBackend>::with_configuration(
            ExecutionProverConfiguration::for_mode(soundness_mode),
        );
        let program = vec![0x0001_2083, 0xffdf_f06f];
        for (kind, profile) in [
            (ExecutionKind::Unified22, ProofProfile::CompressionFinal),
            (ExecutionKind::Unified, ProofProfile::Compression),
            (ExecutionKind::L1Wrap, ProofProfile::L1Wrap),
        ] {
            let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                prover.add_binary_variants(
                    program.clone(),
                    program.clone(),
                    &[(kind, MachineType::Reduced, &[profile])],
                    Some(32),
                )
            }))
            .map(|handle| panic!("{profile:?}: registered as {handle:?}"))
            .unwrap_err();
            let message = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .unwrap_or_default();
            assert!(
                message.contains("supports only the pessimistic-conjecture soundness mode"),
                "{profile:?}: {message}"
            );
            assert_eq!(prover.next_binary_id, 0);
            assert!(prover.binary_holders.is_empty());
        }
    }
}
