use super::*;

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Register the requested execution variants of one binary at initialization.
    /// Padding, instruction decoding and family projections are shared across variants.
    pub fn add_binary_variants(
        &mut self,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        variants: &[(ExecutionKind, MachineType)],
        cycles_bound: Option<u32>,
    ) -> Vec<BinaryHandle> {
        assert!(
            !variants.is_empty(),
            "at least one binary variant is required"
        );
        for (i, variant) in variants.iter().enumerate() {
            assert!(!variants[..i].contains(variant), "duplicate binary variant");
        }
        let decode_start = Instant::now();
        let mut padded_binary_image = binary_image.clone();
        crate::upstream::pad_bytecode_for_proving(&mut padded_binary_image);
        let mut machines = Vec::new();
        for &(_, machine) in variants {
            if machines
                .iter()
                .any(|(prepared_machine, _, _)| *prepared_machine == machine)
            {
                continue;
            }
            let kinds: Vec<_> = variants
                .iter()
                .filter_map(|&(kind, m)| (m == machine).then_some(kind))
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
        for &(execution_kind, machine_type) in variants {
            let key = self.next_binary_id;
            info!(
                "PROVER inserting binary with key {key:?} ({execution_kind:?}, {machine_type:?})"
            );
            let (_, preprocessing, instruction_tape) = machines
                .iter()
                .find(|(machine, _, _)| *machine == machine_type)
                .unwrap();
            let circuit_types =
                crate::setup::circuit_types_for_variant(execution_kind, machine_type);
            let mut setup_time = std::time::Duration::ZERO;
            let mut preparation_time = std::time::Duration::ZERO;
            let precomputations: HashMap<_, _> = circuit_types.into_iter().map(|circuit_type| {
                debug!("PROVER producing precomputations for circuit {circuit_type:?} and binary with key {key:?}");
                let start = Instant::now();
                let setup = build_unrolled_setup_with_preprocessing(circuit_type, &padded_binary_image, preprocessing, &self.worker);
                setup_time += start.elapsed();
                let start = Instant::now();
                let precomp = self.backend.prepare(CircuitType::Unrolled(circuit_type), setup, self.configuration.soundness_mode);
                preparation_time += start.elapsed();
                (circuit_type, precomp)
            }).collect();
            let start = Instant::now();
            request_setup_initialization(
                &self.backend,
                precomputations
                    .iter()
                    .map(|(circuit_type, precomp)| {
                        (CircuitType::Unrolled(*circuit_type), precomp.clone())
                    })
                    .collect(),
            )
            .wait();
            info!("PROVER inserted binary with key {key:?}: CPU setup construction {setup_time:?}, backend preparation {preparation_time:?}, setup initialization {:?}", start.elapsed());
            let holder = BinaryHolder {
                execution_kind,
                machine_type,
                binary_image: Arc::clone(&binary_image),
                text_section: Arc::clone(&text_section),
                cycles_bound,
                instruction_tape: Arc::clone(instruction_tape),
                jit_cache: Arc::new(Mutex::new(TypeMap::new())),
                precomputations,
            };
            assert!(self.binary_holders.insert(key, holder).is_none());
            self.next_binary_id += 1;
            handles.push(BinaryHandle(key));
        }
        handles
    }
}
