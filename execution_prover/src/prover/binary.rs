use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    pub fn add_binary(
        &mut self,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        cycles_bound: Option<u32>,
        profiles: &[ProofProfile],
    ) -> BinaryHandle {
        self.try_add_binary(
            execution_kind,
            machine_type,
            binary_image,
            text_section,
            cycles_bound,
            profiles,
        )
        .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Register a binary without panicking on an unavailable selected config.
    pub fn try_add_binary(
        &mut self,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        cycles_bound: Option<u32>,
        profiles: &[ProofProfile],
    ) -> Result<BinaryHandle, crate::config::SelectionError> {
        assert!(
            !profiles.is_empty(),
            "add_binary needs at least one ProofProfile"
        );
        let mut profiles = profiles.to_vec();
        profiles.sort_unstable();
        profiles.dedup();
        if execution_kind.is_l1_wrap() || profiles.contains(&ProofProfile::L1Wrap) {
            assert!(
                execution_kind.is_l1_wrap(),
                "ProofProfile::L1Wrap requires ExecutionKind::L1Wrap21"
            );
            assert_eq!(
                profiles,
                [ProofProfile::L1Wrap],
                "ExecutionKind::{execution_kind:?} requires exactly ProofProfile::L1Wrap"
            );
            assert_eq!(
                machine_type,
                MachineType::Reduced,
                "ExecutionKind::{execution_kind:?} requires MachineType::Reduced"
            );
        }
        if profiles.contains(&ProofProfile::L1Feeder) {
            assert_eq!(
                execution_kind,
                ExecutionKind::Unified22,
                "ProofProfile::L1Feeder requires ExecutionKind::Unified22"
            );
        }
        if profiles.contains(&ProofProfile::L1FeederA) {
            assert_eq!(
                execution_kind,
                ExecutionKind::Unified,
                "ProofProfile::L1FeederA requires ExecutionKind::Unified"
            );
        }
        match execution_kind {
            ExecutionKind::Unified => assert!(
                profiles
                    .iter()
                    .all(|profile| matches!(profile, ProofProfile::Standard | ProofProfile::L1FeederA)),
                "ExecutionKind::Unified admits only ProofProfile::Standard and ProofProfile::L1FeederA, got {profiles:?}"
            ),
            ExecutionKind::Unified22 => assert_eq!(
                profiles,
                [ProofProfile::L1Feeder],
                "ExecutionKind::Unified22 requires exactly ProofProfile::L1Feeder"
            ),
            ExecutionKind::Unrolled | ExecutionKind::L1Wrap21 => {}
        }
        // The L1 profiles exist only under PessimisticConjecture (deferred product scope):
        // reject before admission, setup building or backend preparation.
        for profile in &profiles {
            profile
                .config_profile()
                .validate_selection(self.configuration.selection())?;
        }
        self.backend
            .admit_binary(execution_kind, machine_type, &profiles);
        let key = self.next_binary_id;
        info!("PROVER inserting binary with key {key:?}");
        let preprocessed_bytecode = match machine_type {
            MachineType::Full => {
                preprocess_bytecode::<FullMachineDecoderConfig, true>(&text_section)
            }
            MachineType::FullUnsigned => {
                preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section)
            }
            MachineType::Reduced => {
                preprocess_bytecode::<ReducedMachineDecoderConfig, true>(&text_section)
            }
        };
        let instruction_tape = Arc::new(SimpleTape::new(&preprocessed_bytecode));
        let circuit_types = match execution_kind {
            ExecutionKind::Unrolled => {
                let memory =
                    UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .iter()
                        .copied()
                        .map(UnrolledCircuitType::Memory);
                let non_memory =
                    UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine_type)
                        .iter()
                        .copied()
                        .map(UnrolledCircuitType::NonMemory);
                memory.chain(non_memory).collect_vec()
            }
            ExecutionKind::Unified | ExecutionKind::Unified22 => {
                assert_eq!(
                    machine_type,
                    MachineType::Reduced,
                    "Unified execution kinds are only supported for Reduced machine type"
                );
                let CircuitType::Unrolled(circuit_type) = execution_kind.unified_circuit().unwrap()
                else {
                    unreachable!()
                };
                vec![circuit_type]
            }
            ExecutionKind::L1Wrap21 => vec![],
        };
        let rom = execution_kind.rom();
        let mut padded_binary_image = binary_image.clone();
        crate::upstream::pad_bytecode_for_proving_with_rom(&mut padded_binary_image, rom);
        let mut padded_text_section = text_section.clone();
        crate::upstream::pad_bytecode_for_proving_with_rom(&mut padded_text_section, rom);
        let precomputations: HashMap<_, _> = circuit_types
            .into_iter()
            .map(|circuit_type| {
                debug!(
                    "PROVER producing precomputations for circuit {circuit_type:?} and binary with key {key:?}"
                );
                let setup = build_unrolled_setup(
                    machine_type,
                    circuit_type,
                    &padded_binary_image,
                    &padded_text_section,
                    &self.worker,
                );
                let precomp = self.backend.prepare_with_selection(
                    CircuitType::Unrolled(circuit_type),
                    setup,
                    self.configuration.selection(),
                    &profiles,
                )?;
                Ok((circuit_type, precomp))
            })
            .collect::<Result<_, crate::config::SelectionError>>()?;
        let l1_wrap_circuit = execution_kind
            .is_l1_wrap()
            .then(|| execution_kind.unified_circuit().unwrap());
        let l1_wrap_precomputations = l1_wrap_circuit
            .map(|circuit_type| {
                assert_eq!(circuit_type, CircuitType::L1Wrap21);
                let setup = unified_reduced_machine_proth120::l1_wrap_2p21::l1_wrap_setup(
                    &padded_binary_image,
                    &padded_text_section,
                );
                assert_eq!(setup.trace_len, circuit_type.get_domain_size());
                assert_eq!(setup.rom, circuit_type.rom());
                assert_eq!(
                    setup.circuit.memory_layout.teardown_sets.len(),
                    circuit_type.get_num_inits_and_teardowns_sets()
                );
                self.backend.prepare_with_selection(
                    circuit_type,
                    crate::setup::CanonicalCircuitSetup::L1Wrap(setup),
                    self.configuration.selection(),
                    &profiles,
                )
            })
            .transpose()?;
        let pending_setup_initialization = request_setup_initialization(
            &self.backend,
            self.configuration.selection(),
            precomputations
                .iter()
                .map(|(circuit_type, precomp)| {
                    (CircuitType::Unrolled(*circuit_type), precomp.clone())
                })
                .chain(l1_wrap_circuit.zip(l1_wrap_precomputations.clone()))
                .collect(),
        );
        pending_setup_initialization.wait();
        let binary_image = Arc::new(binary_image.into_boxed_slice());
        let text_section = Arc::new(text_section.into_boxed_slice());
        let jit_cache = Arc::new(Mutex::new(TypeMap::new()));
        let holder = BinaryHolder {
            execution_kind,
            profiles,
            machine_type,
            binary_image,
            text_section,
            cycles_bound,
            instruction_tape,
            jit_cache,
            precomputations,
            l1_wrap_precomputations,
        };
        assert!(self.binary_holders.insert(key, holder).is_none());
        self.next_binary_id += 1;
        Ok(BinaryHandle(key))
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::config::{ProvingSelection, SelectionError, SoundnessMode};
    use crate::messages::WorkBatch;
    use crate::setup::CanonicalCircuitSetup;
    use crate::test_support::{TestBackend, TestConfiguration};
    use crate::upstream::SecurityLevel;
    use ::prover::definitions::ProverConfigProfile;
    use ::prover::gkr::prover_config::example_configs::ConfigSelectionError;
    use riscv_transpiler::jit::JitRunnerRam;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use worker::Worker;

    /// `TestBackend` that accepts every mode and counts admissions and preparations, so the
    /// L1 capability check in `try_add_binary` is observable without CUDA or a real backend.
    struct ProbeBackend {
        inner: TestBackend,
        admitted: AtomicUsize,
        prepared: AtomicUsize,
    }

    impl ExecutionBackend for ProbeBackend {
        type Configuration = TestConfiguration;
        type Allocator = <TestBackend as ExecutionBackend>::Allocator;
        type Memory = <TestBackend as ExecutionBackend>::Memory;
        type Snapshot = <TestBackend as ExecutionBackend>::Snapshot;
        type Precomputations = <TestBackend as ExecutionBackend>::Precomputations;

        fn validate_selection(_: ProvingSelection) -> Result<(), SelectionError> {
            Ok(())
        }
        fn initialize(
            config: &ExecutionProverConfiguration<TestConfiguration>,
            worker: Arc<Worker>,
        ) -> Self {
            Self {
                inner: TestBackend::initialize(config, worker),
                admitted: AtomicUsize::new(0),
                prepared: AtomicUsize::new(0),
            }
        }
        fn allocate_trace_block(&self, bytes: usize) -> Self::Allocator {
            self.inner.allocate_trace_block(bytes)
        }
        fn allocate_memory(&self, ram: JitRunnerRam) -> Self::Memory {
            self.inner.allocate_memory(ram)
        }
        fn allocate_snapshot(&self) -> Self::Snapshot {
            self.inner.allocate_snapshot()
        }
        fn admit_binary(
            &self,
            execution_kind: ExecutionKind,
            machine_type: MachineType,
            profiles: &[ProofProfile],
        ) {
            self.admitted.fetch_add(1, Ordering::SeqCst);
            self.inner
                .admit_binary(execution_kind, machine_type, profiles);
        }
        fn prepare(
            &self,
            circuit: CircuitType,
            setup: CanonicalCircuitSetup,
            security: SecurityLevel,
            profiles: &[ProofProfile],
        ) -> Self::Precomputations {
            self.prepared.fetch_add(1, Ordering::SeqCst);
            self.inner.prepare(circuit, setup, security, profiles)
        }
        fn submit(&self, batch: WorkBatch<Self::Allocator, Self::Precomputations>) {
            self.inner.submit(batch)
        }
    }

    /// Every L1 profile under ethproofs is rejected with the deferred-scope config error
    /// before the backend admits the binary or prepares a setup, and no binary is registered.
    #[test]
    fn ethproofs_l1_binary_is_rejected_before_admission() {
        let selection = ProvingSelection {
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProvingSelection::default()
        };
        let mut prover = ExecutionProver::<ProbeBackend>::with_configuration(
            ExecutionProverConfiguration::for_selection(selection),
        );
        let prepared = prover.backend().prepared.load(Ordering::SeqCst);
        assert!(prepared > 0, "the probe counts the common preparations");
        let program = vec![0x0001_2083, 0xffdf_f06f];
        for (kind, profile, config_profile) in [
            (
                ExecutionKind::Unified22,
                ProofProfile::L1Feeder,
                ProverConfigProfile::L1Feeder,
            ),
            (
                ExecutionKind::Unified,
                ProofProfile::L1FeederA,
                ProverConfigProfile::L1Feeder,
            ),
            (
                ExecutionKind::L1Wrap21,
                ProofProfile::L1Wrap,
                ProverConfigProfile::EvmProductionPacked,
            ),
        ] {
            let result = prover.try_add_binary(
                kind,
                MachineType::Reduced,
                program.clone(),
                program.clone(),
                Some(32),
                &[profile],
            );
            match result {
                Err(SelectionError::ConfigSelection(
                    ConfigSelectionError::UnsupportedSpecialConfigMode {
                        profile: rejected,
                        mode: SoundnessMode::EthproofsSoundnessCalc,
                    },
                )) => assert_eq!(rejected, config_profile, "{profile:?}"),
                Err(error) => panic!("{profile:?}: unexpected error {error}"),
                Ok(handle) => panic!("{profile:?}: registered as {handle:?}"),
            }
            assert_eq!(prover.backend().admitted.load(Ordering::SeqCst), 0);
            assert_eq!(prover.backend().prepared.load(Ordering::SeqCst), prepared);
            assert_eq!(prover.next_binary_id, 0);
            assert!(prover.binary_holders.is_empty());
        }
    }
}
