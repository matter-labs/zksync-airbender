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
        self.backend
            .admit_binary(execution_kind, machine_type, &profiles);
        let key = self.next_binary_id;
        self.next_binary_id += 1;
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
                let precomp = self.backend.prepare(
                    CircuitType::Unrolled(circuit_type),
                    setup,
                    self.configuration.security_level,
                    &profiles,
                );
                (circuit_type, precomp)
            })
            .collect();
        let l1_wrap_circuit = execution_kind
            .is_l1_wrap()
            .then(|| execution_kind.unified_circuit().unwrap());
        let l1_wrap_precomputations = l1_wrap_circuit.map(|circuit_type| {
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
            self.backend.prepare(
                circuit_type,
                crate::setup::CanonicalCircuitSetup::L1Wrap(setup),
                self.configuration.security_level,
                &profiles,
            )
        });
        let pending_setup_initialization = request_setup_initialization(
            &self.backend,
            self.configuration.security_level,
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
        BinaryHandle(key)
    }
}
