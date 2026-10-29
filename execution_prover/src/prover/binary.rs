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
        let variants: Vec<_> = variants.iter().map(|&(execution_kind, machine_type, profiles)| {
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
            self.backend.admit_binary(execution_kind, machine_type, &profiles);
            (execution_kind, machine_type, profiles)
        }).collect();
        for (i, (kind, machine, _)) in variants.iter().enumerate() {
            assert!(
                !variants[..i]
                    .iter()
                    .any(|(k, m, _)| (k, m) == (kind, machine)),
                "duplicate binary variant"
            );
        }
        let decode_start = Instant::now();
        let mut machines = Vec::new();
        for &(kind, machine, _) in &variants {
            if kind.is_l1_wrap() || machines.iter().any(|(m, _, _)| *m == machine) {
                continue;
            }
            let kinds: Vec<_> = variants
                .iter()
                .filter_map(|(k, m, _)| (*m == machine && !k.is_l1_wrap()).then_some(*k))
                .collect();
            let preprocessing = preprocess_binary(machine, &kinds, &text_section);
            let tape = Arc::new(SimpleTape::new(&preprocessing.execution_instructions));
            machines.push((machine, preprocessing, tape));
        }
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
            let key = self.next_binary_id;
            info!(
                "PROVER inserting binary with key {key:?} ({execution_kind:?}, {machine_type:?})"
            );
            let rom = execution_kind.rom();
            let mut padded_binary_image = binary_image.to_vec();
            let mut padded_text_section = text_section.to_vec();
            crate::upstream::pad_bytecode_for_proving_with_rom(&mut padded_binary_image, rom);
            crate::upstream::pad_bytecode_for_proving_with_rom(&mut padded_text_section, rom);
            let ordinary = machines
                .iter()
                .find(|(machine, _, _)| *machine == machine_type);
            let instruction_tape = if execution_kind.is_l1_wrap() {
                Arc::new(SimpleTape::new(
                    &riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode::<
                        riscv_transpiler::ir::ReducedMachineDecoderConfig,
                        true,
                    >(&text_section),
                ))
            } else {
                Arc::clone(&ordinary.unwrap().2)
            };
            let circuit_types =
                crate::setup::circuit_types_for_variant(execution_kind, machine_type);
            let mut setup_time = std::time::Duration::ZERO;
            let mut preparation_time = std::time::Duration::ZERO;
            let precomputations: HashMap<_, _> = circuit_types.into_iter().map(|circuit_type| {
                debug!("PROVER producing precomputations for circuit {circuit_type:?} and binary with key {key:?}");
                let start = Instant::now();
                let setup = build_unrolled_setup_with_preprocessing(circuit_type, &padded_binary_image, &ordinary.unwrap().1, &self.worker);
                setup_time += start.elapsed();
                let start = Instant::now();
                let precomp = self.backend.prepare(CircuitType::Unrolled(circuit_type), setup, self.configuration.soundness_mode, &profiles);
                preparation_time += start.elapsed();
                (circuit_type, precomp)
            }).collect();
            let l1_wrap_circuit = execution_kind
                .is_l1_wrap()
                .then(|| execution_kind.unified_circuit().unwrap());
            let l1_wrap_precomputations = l1_wrap_circuit.map(|circuit_type| {
                assert_eq!(circuit_type, CircuitType::L1Wrap21);
                let setup = unified_reduced_machine_proth120::l1_wrap_2p21::l1_wrap_setup(
                    &padded_binary_image,
                    &padded_text_section,
                    &self.worker,
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
                    self.configuration.soundness_mode,
                    &profiles,
                )
            });
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
                    .chain(l1_wrap_circuit.zip(l1_wrap_precomputations.clone()))
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
