//! Single-cycle satisfiability of the unified extended machine
//! (`cs::gkr_circuits::unified_extended_machine`) on real programs: every replayed cycle of a
//! program with MUL/MULHU and sub-word memory accesses is run through the circuit with the
//! write-value oracle poisoned (the self-generating witness contract).
use super::*;

#[cfg(test)]
pub(super) mod test {
    use super::*;
    use crate::tests::gkr::orchestration::common::{run_vm_and_capture, ProgramConfig};
    use crate::tests::gkr::orchestration::unified::replay_unified_cycles;
    use common_constants::circuit_families::EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX;
    use cs::gkr_circuits::unified_extended_machine::*;
    use field::baby_bear::base::BabyBearField;
    use field::proth120::Proth120;
    use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, InstructionName};
    use riscv_transpiler::ir::ExtendedMachineDecoderConfig;
    use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters};
    use riscv_transpiler::witness::data_structs::MEM_LOAD_TRACE_DATA_MARKER;

    /// Replay a program under the extended decoding config; returns the cycles, the text
    /// section (the decoder table source) and the opcode names per PC. The replayer zeroes the read value
    /// of every load in the ROM address range (the reduced machine recovers those words through
    /// its ROM lookup table). The extended machine has no ROM range: such a load is an ordinary
    /// RAM read of a cell nothing ever writes, so its value is the ROM image word.
    pub(super) fn program_witness(
        config: ProgramConfig,
    ) -> (
        Vec<UnifiedOpcodeTracingDataWithTimestamp>,
        Vec<u32>,
        Vec<InstructionName>,
    ) {
        let worker = worker::Worker::new_with_num_threads(2);
        let vm = run_vm_and_capture::<DelegationsAndUnifiedCounters, ExtendedMachineDecoderConfig>(
            &config, &worker,
        );
        let num_calls = vm
            .counters
            .get_calls_to_circuit_family::<EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX>();
        let mut witness = replay_unified_cycles(&vm, num_calls);
        let rom_bound = 1u32 << (16 + common_constants::ROM_SECOND_WORD_BITS);
        for wit in witness.iter_mut() {
            if let UnifiedOpcodeTracingDataWithTimestamp::Mem(inner) = wit {
                if inner.discr == MEM_LOAD_TRACE_DATA_MARKER
                    && inner.opcode_data.aligned_ram_address < rom_bound
                {
                    let word = (inner.opcode_data.aligned_ram_address / 4) as usize;
                    inner.opcode_data.aligned_ram_read_value =
                        vm.binary.get(word).copied().unwrap_or(0);
                }
            }
        }
        let names = preprocess_bytecode::<ExtendedMachineDecoderConfig, false>(&vm.text_section)
            .into_iter()
            .map(|instr| instr.name)
            .collect();
        (witness, vm.text_section, names)
    }

    /// Delegation calls write rd = x0 := 0 straight from the trace (Family 1 derives no write
    /// value for them, in either unified machine), so only those rows see the real oracle.
    fn check_cycle<F: PrimeField>(
        wit: UnifiedOpcodeTracingDataWithTimestamp,
        text_section: &[u32],
        is_delegation: bool,
    ) {
        let tables = |cs: &mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>| {
            unified_extended_machine_table_addition_fn::<F, _>(cs)
        };
        let circuit = |cs: &mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>| {
            unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr::<F, _>(cs)
        };
        if is_delegation {
            test_single_unified_cycle::<F, ExtendedMachineDecoderConfig>(
                UnifiedExtendedMachineDecoder,
                wit,
                text_section,
                tables,
                circuit,
            )
        } else {
            test_single_unified_cycle_with_oracle::<F, ExtendedMachineDecoderConfig, _>(
                UnifiedExtendedMachineDecoder,
                wit,
                text_section,
                tables,
                circuit,
                PoisonedWriteValueOracle,
            )
        }
    }

    fn is_new_family_opcode(name: InstructionName) -> bool {
        use InstructionName::*;
        matches!(name, Lb | Lbu | Lh | Lhu | Sb | Sh | Mul | Mulhu)
    }

    /// Every cycle of the new families and a prefix of all cycles; counts what was covered so
    /// a program that happens not to exercise an opcode is noticed.
    fn check_program<F: PrimeField>(
        config: ProgramConfig,
        all_cycles_prefix: usize,
        required: &[InstructionName],
    ) {
        let (witness, text_section, names) = program_witness(config);
        let mut covered: Vec<(InstructionName, usize)> = Vec::new();
        let mut checked = 0usize;
        for (i, wit) in witness.into_iter().enumerate() {
            let name = names[(wit.initial_pc() / 4) as usize];
            if i >= all_cycles_prefix && !is_new_family_opcode(name) {
                continue;
            }
            check_cycle::<F>(wit, &text_section, name == InstructionName::ZicsrDelegation);
            match covered.iter_mut().find(|(n, _)| *n == name) {
                Some((_, count)) => *count += 1,
                None => covered.push((name, 1)),
            }
            checked += 1;
        }
        println!("checked {checked} cycles: {covered:?}");
        for required in required {
            assert!(
                covered.iter().any(|(n, _)| n == required),
                "{required:?} not exercised by this program"
            );
        }
    }

    /// `examples/extended_machine_smoke`: every sub-word variant at every byte offset,
    /// negative immediates, MUL/MULHU edge operands.
    pub(super) fn smoke_program() -> ProgramConfig {
        ProgramConfig {
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/extended_machine_smoke/app.bin",
                "../examples/extended_machine_smoke/app.text",
            ),
            non_determinism_reads: vec![],
            cycles_bound: 1 << 20,
            ram_bound_bytes: 1 << 30,
        }
    }

    const ALL_NEW_OPCODES: &[InstructionName] = &[
        InstructionName::Lb,
        InstructionName::Lbu,
        InstructionName::Lh,
        InstructionName::Lhu,
        InstructionName::Sb,
        InstructionName::Sh,
        InstructionName::Lw,
        InstructionName::Sw,
        InstructionName::Mul,
        InstructionName::Mulhu,
    ];

    #[test]
    fn extended_machine_smoke_self_generates_write_values() {
        check_program::<BabyBearField>(smoke_program(), usize::MAX, ALL_NEW_OPCODES);
    }

    /// `hashed_fibonacci`: MUL/MULHU from the magic-number divide plus every reduced-machine
    /// family and a Blake2s G-function delegation.
    #[test]
    fn extended_machine_hashed_fibonacci_self_generates_write_values() {
        check_program::<BabyBearField>(
            ProgramConfig::hashed_fibonacci_blake_g_function(),
            2000,
            &[InstructionName::Mul, InstructionName::Mulhu],
        );
    }

    /// `keccak_f1600`: byte loads around the keccak delegation.
    #[test]
    fn extended_machine_keccak_f1600_self_generates_write_values() {
        check_program::<BabyBearField>(
            ProgramConfig::keccak_f1600(),
            2000,
            &[InstructionName::Lbu],
        );
    }

    /// The two-field (Proth120 circuit, BabyBear mop) instantiation.
    #[test]
    fn extended_machine_smoke_large_field() {
        check_program::<Proth120>(smoke_program(), usize::MAX, ALL_NEW_OPCODES);
    }
}

/// Negative single-cycle tests: the constraints and lookups, not just the witness derivation,
/// bind the write values and the word-cell address.
#[cfg(test)]
mod negative {
    use super::test::*;
    use super::*;
    use cs::definitions::Variable;
    use cs::gkr_circuits::unified_extended_machine::*;
    use field::baby_bear::base::BabyBearField;
    use field::Field;
    use riscv_transpiler::ir::simple_instruction_set::InstructionName;
    use riscv_transpiler::ir::ExtendedMachineDecoderConfig;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    type F = BabyBearField;

    /// Build the circuit for one replayed cycle and return its finalized statement plus the
    /// debug witness as a dense assignment (unassigned variables read as 0).
    fn finalized_row<O: ::cs::oracle::Oracle<F> + 'static>(
        wit: UnifiedOpcodeTracingDataWithTimestamp,
        text_section: &[u32],
        wrap_oracle: impl FnOnce(UnifiedRiscvCircuitOracle<'static>) -> O,
    ) -> (cs::cs::circuit_output::CircuitOutput<F>, Vec<F>) {
        let mut t = process_binary_into_separate_tables_ext::<
            F,
            ExtendedMachineDecoderConfig,
            true,
            Global,
        >(
            text_section,
            &[Box::new(UnifiedExtendedMachineDecoder)],
            1 << 20,
            &[NON_DETERMINISM_CSR as u16],
        );
        let decoder_data = t
            .remove(&UnifiedExtendedMachineDecoder.instruction_family_index())
            .expect("decoder data");
        let oracle = UnifiedRiscvCircuitOracle {
            inner: &[wit],
            decoder_table: &decoder_data,
        };
        let oracle: UnifiedRiscvCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let oracle = (wrap_oracle)(oracle);
        let preprocessed: Vec<_> = decoder_data
            .iter()
            .map(|el| el.unwrap_or_default())
            .collect();
        let mut cs = BasicAssembly::<F, CSDebugWitnessEvaluator<F>, false>::new_with_oracle_and_preprocessed_decoder(oracle, preprocessed);
        unified_extended_machine_table_addition_fn::<F, _>(&mut cs);
        unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr::<F, _>(&mut cs);
        let (output, placer) = cs.finalize();
        let placer = placer.expect("debug evaluator");
        let values = (0..output.num_of_variables as u64)
            .map(|i| placer.get_value(Variable(i)).unwrap_or(F::ZERO))
            .collect();
        (output, values)
    }

    fn eval_constraint(constraint: &cs::constraint::Constraint<F>, values: &[F]) -> F {
        let (quad, linear, constant) = constraint.clone().split_max_quadratic();
        let mut value = constant;
        for (coeff, a, b) in quad {
            let mut t = coeff;
            t.mul_assign(&values[a.0 as usize]);
            t.mul_assign(&values[b.0 as usize]);
            value.add_assign(&t);
        }
        for (coeff, a) in linear {
            let mut t = coeff;
            t.mul_assign(&values[a.0 as usize]);
            value.add_assign(&t);
        }
        value
    }

    fn eval_lookup_input(input: &cs::definitions::LookupInput<F>, values: &[F]) -> F {
        use cs::definitions::LookupInput;
        match input {
            LookupInput::Variable(v) => values[v.0 as usize],
            LookupInput::Expression {
                linear_terms,
                constant_coeff,
            } => {
                let mut value = *constant_coeff;
                for (coeff, v) in linear_terms {
                    let mut t = *coeff;
                    t.mul_assign(&values[v.0 as usize]);
                    value.add_assign(&t);
                }
                value
            }
        }
    }

    /// Re-check the whole row statement from the base-layer assignment: every intermediate
    /// variable is recomputed from its defining expression (in definition order), then every
    /// constraint, Booleanity, range check and lookup is checked. Unlike the debug evaluator's
    /// eager construction-time checks, this sees values changed AFTER construction, which is
    /// what lets a negative test tamper with a derived witness value.
    fn row_satisfied(
        output: &cs::cs::circuit_output::CircuitOutput<F>,
        values: &mut [F],
    ) -> Result<(), String> {
        use cs::cs::circuit::LookupQueryTableType;
        use cs::structured_expr::StructuredStatement;
        for stmt in output.structured_statements.iter() {
            match stmt {
                StructuredStatement::Define {
                    dst,
                    compiled_constraint,
                    ..
                } => {
                    values[dst.0 as usize] = eval_constraint(compiled_constraint, values);
                }
                StructuredStatement::AssertZero {
                    compiled_constraint,
                    ..
                } => {
                    let value = eval_constraint(compiled_constraint, values);
                    if value != F::ZERO {
                        return Err(format!("constraint {compiled_constraint} = {value}"));
                    }
                }
            }
        }
        for v in output.boolean_vars.iter() {
            let value = values[v.0 as usize];
            if value != F::ZERO && value != F::ONE {
                return Err(format!("{v:?} = {value} is not Boolean"));
            }
        }
        for rc in output.range_check_expressions.iter() {
            let value = eval_lookup_input(&rc.input, values).as_u32_reduced();
            if value >= 1u32 << rc.width {
                return Err(format!("{value} fails the {}-bit range check", rc.width));
            }
        }
        for (i, lookup) in output.lookups.iter().enumerate() {
            let row: Vec<F> = lookup
                .row
                .iter()
                .map(|input| eval_lookup_input(input, values))
                .collect();
            let table_id = match &lookup.table {
                LookupQueryTableType::Constant(t) => *t as u32,
                LookupQueryTableType::Variable(v) => values[v.0 as usize].as_u32_reduced(),
                LookupQueryTableType::Expression(e) => {
                    eval_lookup_input(e, values).as_u32_reduced()
                }
            };
            let cs::tables::LookupWrapper::Initialized(table) =
                &output.table_driver.tables[table_id as usize]
            else {
                return Err(format!("lookup {i}: table {table_id} is not initialized"));
            };
            // `lookup_row` panics on a key outside the table, but with a pure index function it
            // does not compare the value columns; compare the full row against the content.
            let Ok(index) = catch_unwind(AssertUnwindSafe(|| table.lookup_row(&row))) else {
                return Err(format!("lookup {i}: {row:?} not in table {table_id}"));
            };
            let width = table.width();
            if table.data[index][..width] != row[..width.min(row.len())]
                || row[width.min(row.len())..].iter().any(|el| !el.is_zero())
            {
                return Err(format!(
                    "lookup {i}: {row:?} differs from table {table_id} row {index} {:?}",
                    &table.data[index][..width]
                ));
            }
        }
        Ok(())
    }

    fn silence_panics() {
        let _ = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
    }

    fn restore_panics() {
        let _ = std::panic::take_hook();
    }

    /// With the derived rd / RAM write value replaced by garbage, every row of the smoke
    /// program is rejected: each family binds its write value by constraints or lookups, not
    /// only by witness derivation.
    #[test]
    fn extended_machine_rejects_wrong_write_values() {
        use cs::cs::circuit_trait::WordRepresentation;
        let (witness, text_section, names) = program_witness(smoke_program());
        silence_panics();
        let mut accepted_rows = vec![];
        let mut rejected = 0;
        for (i, wit) in witness.into_iter().enumerate() {
            let name = names[(wit.initial_pc() / 4) as usize];
            let pc = wit.initial_pc();
            let (output, values) = finalized_row(wit, &text_section, |o| o);
            if let Err(e) = row_satisfied(&output, &mut values.clone()) {
                restore_panics();
                panic!("honest row {i} ({name:?}) rejected: {e}");
            }
            let WordRepresentation::U16Limbs(write_limbs) = output.memory_queries[2].write_value()
            else {
                unreachable!()
            };
            for (limb, garbage) in write_limbs.into_iter().zip([0xBEEF, 0x0001]) {
                let mut tampered = values.clone();
                tampered[limb.0 as usize] = F::from_u32_unchecked(garbage);
                if row_satisfied(&output, &mut tampered).is_ok() {
                    accepted_rows.push((i, pc, name));
                } else {
                    rejected += 1;
                }
            }
        }
        restore_panics();
        assert!(
            accepted_rows.is_empty(),
            "rows accepting a wrong write value: {accepted_rows:?}"
        );
        assert!(rejected > 100);
    }

    /// Oracle wrapper that moves every RAM cell address off its word alignment.
    struct MisalignedCellOracle<O>(O);

    impl<F: PrimeField, O: ::cs::oracle::Oracle<F>> ::cs::oracle::Oracle<F>
        for MisalignedCellOracle<O>
    {
        fn get_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            subindex: usize,
            trace_row: usize,
        ) -> F {
            self.0
                .get_witness_from_placeholder(placeholder, subindex, trace_row)
        }
        fn get_u32_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u32 {
            let value = self
                .0
                .get_u32_witness_from_placeholder(placeholder, trace_row);
            if matches!(placeholder, Placeholder::ShuffleRamAddress(_)) && value >= 32 {
                value + 1
            } else {
                value
            }
        }
        fn get_u16_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u16 {
            self.0
                .get_u16_witness_from_placeholder(placeholder, trace_row)
        }
        fn get_u8_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u8 {
            self.0
                .get_u8_witness_from_placeholder(placeholder, trace_row)
        }
        fn get_boolean_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> bool {
            self.0
                .get_boolean_witness_from_placeholder(placeholder, trace_row)
        }
        fn get_timestamp_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> cs::definitions::TimestampScalar {
            self.0
                .get_timestamp_witness_from_placeholder(placeholder, trace_row)
        }
        fn get_executor_family_data(
            &self,
            trace_row: usize,
        ) -> cs::gkr_circuits::ExecutorFamilyDecoderData {
            self.0.get_executor_family_data(trace_row)
        }
    }

    /// A RAM cell that is not word-aligned is rejected by every load/store.
    #[test]
    fn extended_machine_rejects_misaligned_cells() {
        use InstructionName::*;
        let (witness, text_section, names) = program_witness(smoke_program());
        silence_panics();
        let mut rejected = 0;
        for wit in witness {
            let name = names[(wit.initial_pc() / 4) as usize];
            let is_memory = matches!(name, Lb | Lbu | Lh | Lhu | Lw | Sb | Sh | Sw);
            let accepted = catch_unwind(AssertUnwindSafe(|| {
                let (output, mut values) = finalized_row(wit, &text_section, MisalignedCellOracle);
                row_satisfied(&output, &mut values).is_ok()
            }))
            .unwrap_or(false);
            assert_eq!(accepted, !is_memory, "{name:?}");
            rejected += is_memory as usize;
        }
        restore_panics();
        assert!(rejected > 30);
    }
}
