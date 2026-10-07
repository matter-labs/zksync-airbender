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
        if execution_kind == ExecutionKind::L1Wrap || profiles.contains(&ProofProfile::L1Wrap) {
            assert_eq!(
                execution_kind,
                ExecutionKind::L1Wrap,
                "ProofProfile::L1Wrap requires ExecutionKind::L1Wrap"
            );
            assert_eq!(
                profiles,
                [ProofProfile::L1Wrap],
                "ExecutionKind::L1Wrap requires exactly ProofProfile::L1Wrap"
            );
            assert_eq!(
                machine_type,
                MachineType::Reduced,
                "ExecutionKind::L1Wrap requires MachineType::Reduced"
            );
        }
        if profiles.contains(&ProofProfile::L1Feeder) {
            assert_eq!(
                execution_kind,
                ExecutionKind::Unified,
                "ProofProfile::L1Feeder requires ExecutionKind::Unified"
            );
        }
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
            ExecutionKind::Unified => {
                assert_eq!(
                    machine_type,
                    MachineType::Reduced,
                    "Unified execution kind is only supported for Reduced machine type"
                );
                vec![UnrolledCircuitType::Unified]
            }
            ExecutionKind::L1Wrap => vec![],
        };
        let mut padded_binary_image = binary_image.clone();
        crate::upstream::pad_bytecode_for_proving(&mut padded_binary_image);
        let mut padded_text_section = text_section.clone();
        crate::upstream::pad_bytecode_for_proving(&mut padded_text_section);
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
        let l1_wrap_precomputations = (execution_kind == ExecutionKind::L1Wrap).then(|| {
            use unified_reduced_machine_proth120::{
                l1_wrap_setup, NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2,
            };
            assert_eq!(
                CircuitType::L1Wrap.get_domain_size_log2() as usize,
                TRACE_LEN_LOG2
            );
            assert_eq!(
                CircuitType::L1Wrap.get_num_inits_and_teardowns_sets(),
                NUM_INIT_AND_TEARDOWN_SETS
            );
            self.backend.prepare(
                CircuitType::L1Wrap,
                crate::setup::CanonicalCircuitSetup::L1Wrap(l1_wrap_setup(
                    &padded_binary_image,
                    &padded_text_section,
                )),
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
                .chain(
                    l1_wrap_precomputations
                        .iter()
                        .map(|precomp| (CircuitType::L1Wrap, precomp.clone())),
                )
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
