use super::*;

impl ExecutionProver {
    pub fn add_binary(
        &mut self,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        cycles_bound: Option<u32>,
    ) -> BinaryHandle {
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
        };
        let mut padded_binary_image = binary_image.clone();
        crate::upstream::pad_bytecode_for_proving(&mut padded_binary_image);
        let mut padded_text_section = text_section.clone();
        crate::upstream::pad_bytecode_for_proving(&mut padded_text_section);
        let precomputations = circuit_types
            .into_iter()
            .map(|circuit_type| {
                debug!(
                    "PROVER producing precomputations for circuit {circuit_type:?} and binary with key {key:?}"
                );
                let precomp = build_unrolled_circuit_precomputation(
                    machine_type,
                    circuit_type,
                    &padded_binary_image,
                    &padded_text_section,
                    &self.worker,
                    self.configuration.security_level,
                );
                (circuit_type, precomp)
            })
            .collect();
        let binary_image = Arc::new(binary_image.into_boxed_slice());
        let text_section = Arc::new(text_section.into_boxed_slice());
        let jit_cache = Arc::new(Mutex::new(TypeMap::new()));
        let holder = BinaryHolder {
            execution_kind,
            machine_type,
            binary_image,
            text_section,
            cycles_bound,
            instruction_tape,
            jit_cache,
            precomputations,
        };
        assert!(self.binary_holders.insert(key, holder).is_none());
        BinaryHandle(key)
    }

    pub fn remove_binary(&mut self, handle: BinaryHandle) {
        let key = handle.0;
        info!("PROVER removing binary with key {key:?}");
        assert!(self.binary_holders.remove(&key).is_some());
    }
}
