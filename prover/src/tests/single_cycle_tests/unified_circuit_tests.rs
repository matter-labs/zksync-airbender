use super::*;

#[cfg(test)]
mod test {
    use super::*;
    use ::cs::oracle::Placeholder;
    use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
    use cs::gkr_circuits::unified_reduced_machine::*;
    use field::baby_bear::base::BabyBearField;

    use riscv_transpiler::ir::ReducedMachineDecoderConfig;

    #[expect(
        dead_code,
        reason = "base-field alias kept alongside the Proth120 test paths"
    )]
    type F = BabyBearField;

    fn read_binary(path: &std::path::Path) -> (Vec<u8>, Vec<u32>) {
        use std::io::Read;
        let mut file = std::fs::File::open(path).expect("must open provided file");
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).expect("must read the file");
        assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
        let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
        for el in buffer.as_chunks::<4>().0 {
            binary.push(u32::from_le_bytes(*el));
        }

        (buffer, binary)
    }

    fn test_unified_circuit_circuit<F: PrimeField>(
        opcode_data: UnifiedOpcodeTracingDataWithTimestamp,
        binary: &[u32],
    ) {
        test_single_unified_cycle::<F, ReducedMachineDecoderConfig>(
            UnifiedReducedMachineDecoder,
            opcode_data,
            binary,
            |cs| {
                unified_reduced_machine_table_addition_fn::<F, _>(cs);
                for (table_type, table) in
                    cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                        F,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(binary)
                {
                    cs.add_table_with_content(table_type, table);
                }
            },
            |cs| {
                unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr::<F, _>(cs);
            },
        )
    }

    /// Oracle wrapper that poisons every `ShuffleRamWriteValue` query.
    ///
    /// The `ASSUME_MEMORY_VALUES_ASSIGNED == false` regime has a
    /// self-generating witness contract: the oracle is only trusted for
    /// INPUTS (instruction, register/memory READ values, timestamps); every
    /// family must DERIVE its outputs (the shared rd/mem write-value columns)
    /// in-circuit, gated on its own activity mask. If any family silently
    /// falls back to the oracle for its write value, this wrapper feeds it
    /// garbage and the per-family rd-write constraints reject the row.
    struct PoisonedWriteValueOracle<O>(O);

    impl<F: PrimeField, O: ::cs::oracle::Oracle<F>> ::cs::oracle::Oracle<F>
        for PoisonedWriteValueOracle<O>
    {
        fn get_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            subindex: usize,
            trace_row: usize,
        ) -> F {
            if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
                return F::from_u32_with_reduction(0xBEEF);
            }
            self.0
                .get_witness_from_placeholder(placeholder, subindex, trace_row)
        }

        fn get_u32_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u32 {
            if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
                return 0xDEAD_BEEF;
            }
            self.0
                .get_u32_witness_from_placeholder(placeholder, trace_row)
        }

        fn get_u16_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u16 {
            if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
                return 0xBEEF;
            }
            self.0
                .get_u16_witness_from_placeholder(placeholder, trace_row)
        }

        fn get_u8_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u8 {
            // no write-value placeholder is queried as u8; delegate (must NOT
            // fall through to the trait default, which routes via the field
            // query the inner oracle doesn't support for every placeholder)
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

    #[test]
    fn test_unified_witness_self_generates_write_values() {
        use crate::tests::gkr::bincode_deserialize_from_file;
        use std::path::Path;

        let witness: Vec<UnifiedOpcodeTracingDataWithTimestamp> =
            bincode_deserialize_from_file("unified_proth120_witness.bin");
        let (_, binary) = read_binary(Path::new("../examples/basic_fibonacci/app.bin"));

        for (i, wit) in witness.into_iter().enumerate().skip(10) {
            println!("cycle {}", i);
            test_single_unified_cycle_with_oracle::<BabyBearField, ReducedMachineDecoderConfig, _>(
                UnifiedReducedMachineDecoder,
                wit,
                &binary,
                |cs| {
                    unified_reduced_machine_table_addition_fn::<BabyBearField, _>(cs);
                    for (table_type, table) in
                        cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                            BabyBearField,
                            { common_constants::ROM_SECOND_WORD_BITS },
                        >(&binary)
                    {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                |cs| {
                    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr::<
                        BabyBearField,
                        _,
                    >(cs);
                },
                PoisonedWriteValueOracle,
            );
        }
    }

    #[test]
    fn test_unified_proth120_on_external_witness() {
        use crate::tests::gkr::bincode_deserialize_from_file;
        use std::path::Path;

        let witness: Vec<UnifiedOpcodeTracingDataWithTimestamp> =
            bincode_deserialize_from_file("unified_proth120_witness.bin");
        println!("{} inputs in total", witness.len());
        let (_, binary) = read_binary(Path::new("../examples/basic_fibonacci/app.bin"));

        for (i, wit) in witness.into_iter().enumerate().skip(10) {
            let pc = wit.initial_pc();
            println!("Opcode = 0x{:08x}", binary[(pc as usize) / 4]);
            println!("{}", i);
            if let UnifiedOpcodeTracingDataWithTimestamp::Mem(wit) = wit {
                if wit.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    dbg!(wit.as_load_data());
                } else {
                    dbg!(wit.as_store_data());
                }
            }
            dbg!(&wit);
            test_unified_circuit_circuit::<BabyBearField>(wit, &binary);
        }
    }
}

#[cfg(test)]
mod two_field_mop_tests {
    use super::*;
    use cs::definitions::Variable;
    use cs::gkr_circuits::unified_reduced_machine::{
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr,
        unified_reduced_machine_table_addition_fn, UnifiedReducedMachineDecoder,
    };
    use cs::witness_placer::WitnessPlacer;
    use field::baby_bear::base::BabyBearField;
    use field::{Field, PrimeField, Proth120};
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;
    use std::alloc::Global;

    type F = Proth120;
    type MopF = BabyBearField;

    const BB_P: u32 = 0x7800_0001; // BabyBear prime
    const ADDMOD_FUNCT7: u32 = 0x41; // mop_number = 0 (ADD_MOD)
    const SUBMOD_FUNCT7: u32 = 0x43; // mop_number = 1 (SUB_MOD)
    const MULMOD_FUNCT7: u32 = 0x45; // mop_number = 2 (MUL_MOD)
    const FMAMOD_FUNCT7: u32 = 0x47; // mop_number = 3 (FMA_MOD)

    /// Raw RISC-V `mop.rr` encoding (see `simple_instruction_set.rs`):
    /// `funct7<<25 | rs2<<20 | rs1<<15 | 0b100<<12 | rd<<7 | 0x73`.
    fn encode_mop(funct7: u32, rs1: u32, rs2: u32, rd: u32) -> u32 {
        (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (0b100 << 12) | (rd << 7) | 0x73
    }

    /// Raw RISC-V R-type `ADD rd, rs1, rs2` (funct7 = 0, funct3 = 0, opcode = 0x33).
    fn encode_add(rs1: u32, rs2: u32, rd: u32) -> u32 {
        (rs2 << 20) | (rs1 << 15) | (rd << 7) | 0x33
    }

    fn expected_mulmod(rs1: u32, rs2: u32) -> u32 {
        let mut a = <MopF as PrimeField>::from_raw_repr_with_reduction(rs1);
        let b = <MopF as PrimeField>::from_raw_repr_with_reduction(rs2);

        Field::mul_assign(&mut a, &b);
        a.as_u32_raw_repr_reduced()
    }

    fn expected_addmod(rs1: u32, rs2: u32) -> u32 {
        let mut a = <MopF as PrimeField>::from_raw_repr_with_reduction(rs1);
        let b = <MopF as PrimeField>::from_raw_repr_with_reduction(rs2);

        Field::add_assign(&mut a, &b);
        a.as_u32_raw_repr_reduced()
    }

    fn expected_submod(rs1: u32, rs2: u32) -> u32 {
        let mut a = <MopF as PrimeField>::from_raw_repr_with_reduction(rs1);
        let b = <MopF as PrimeField>::from_raw_repr_with_reduction(rs2);

        Field::sub_assign(&mut a, &b);
        a.as_u32_raw_repr_reduced()
    }

    fn expected_fmamod(rs1: u32, rs2: u32, rd_old: u32) -> u32 {
        let mut a = <MopF as PrimeField>::from_raw_repr_with_reduction(rs1);
        let b = <MopF as PrimeField>::from_raw_repr_with_reduction(rs2);
        let c = <MopF as PrimeField>::from_raw_repr_with_reduction(rd_old);

        Field::fused_mul_add_assign(&mut a, &b, &c);
        a.as_u32_raw_repr_reduced()
    }

    /// Build a NON-canonical raw u32 repr of the same BabyBear element that `reduced` (∈ [0,p))
    /// denotes. `from_raw_repr_with_reduction` maps both `reduced` and `reduced + p` to the SAME
    /// field element (it reduces its argument), yet `reduced + p ∈ [p, 2p) ⊆ [p, u32::MAX]` is a
    /// non-reduced register word — a "raw repr without reduction". `2p < u32::MAX` for BabyBear,
    /// so the offset never wraps. This is exactly the case the mop.rr circuit must handle: a
    /// register may legitimately hold a non-canonical field encoding that has to be reduced before
    /// the modular op, while the emitted output must still be canonical.
    fn non_canonical(reduced: u32) -> u32 {
        assert!(reduced < BB_P, "start from a canonical value (< p)");
        let raw = reduced + BB_P;
        debug_assert_eq!(
            <MopF as PrimeField>::from_raw_repr_with_reduction(raw),
            <MopF as PrimeField>::from_raw_repr_with_reduction(reduced),
            "the +p offset must not change the field element",
        );
        raw
    }

    fn with_two_field_cs<R>(
        opcode: u32,
        rs1_value: u32,
        rs2_value: u32,
        rd_old_value: u32,
        rd_value: u32,
        f: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>) -> R,
    ) -> R {
        let binary = vec![opcode];
        let mut t = process_binary_into_separate_tables_ext::<
            F,
            ReducedMachineDecoderConfig,
            false,
            Global,
        >(
            &binary,
            &[Box::new(UnifiedReducedMachineDecoder)],
            1 << 20,
            &[
                NON_DETERMINISM_CSR as u16,
                BLAKE2S_DELEGATION_CSR_REGISTER as u16,
                BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
            ],
        );
        let decoder_data = t
            .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
            .expect("decoder data");

        let opcode_data = UnifiedOpcodeTracingDataWithTimestamp::NonMem(
            NonMemoryOpcodeTracingDataWithTimestamp {
                opcode_data: NonMemoryOpcodeTracingData {
                    initial_pc: 0,
                    rs1_value,
                    rs2_value,
                    rd_old_value,
                    rd_value,
                    new_pc: 4,
                    delegation_type: 0,
                },
                rs1_read_timestamp: TimestampData::from_scalar(0),
                rs2_read_timestamp: TimestampData::from_scalar(0),
                rd_read_timestamp: TimestampData::from_scalar(0),
                cycle_timestamp: TimestampData::from_scalar(4),
            },
        );

        let oracle = UnifiedRiscvCircuitOracle {
            inner: &[opcode_data],
            decoder_table: &decoder_data,
        };
        let oracle: UnifiedRiscvCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let mut cs = BasicAssembly::<F, CSDebugWitnessEvaluator<F>, false>::new_with_oracle_and_preprocessed_decoder(
            oracle,
            decoder_data
                .iter()
                .map(|el| el.unwrap_or_default())
                .collect::<Vec<_>>(),
        );

        unified_reduced_machine_table_addition_fn::<F, _>(&mut cs);
        for (table_type, table) in
            cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                F,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(&binary)
        {
            cs.add_table_with_content(table_type, table);
        }
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr::<F, _>(&mut cs);

        let result = f(&mut cs);
        drop(cs);
        result
    }

    fn var_by_name(
        cs: &BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>,
        name: &str,
    ) -> Variable {
        cs.variable_names
            .iter()
            .find_map(|(v, n)| (n == name).then_some(*v))
            .unwrap_or_else(|| panic!("missing named variable {name}"))
    }

    fn read_field(cs: &BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>, name: &str) -> F {
        cs.get_value(var_by_name(cs, name))
            .unwrap_or_else(|| panic!("variable {name} left unresolved"))
    }

    fn write_field(
        cs: &mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>,
        name: &str,
        value: F,
    ) {
        let var = var_by_name(cs, name);
        cs.witness_placer
            .as_mut()
            .expect("debug witness placer present")
            .assign_field(var, &value);
    }

    fn k_bit_name(i: usize) -> String {
        format!("shared scratch bool[{}]", i + 2)
    }

    fn read_k_bits(cs: &BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>) -> u32 {
        let mut k = 0u32;
        for i in 0..3 {
            let b = read_field(cs, &k_bit_name(i)).as_u32_reduced();
            k |= (b & 1) << i;
        }
        k
    }

    fn write_k_bits(cs: &mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>, k: u32) {
        assert!(k < 8, "k must fit in three bits");
        for i in 0..3 {
            let bit = (k >> i) & 1;
            write_field(cs, &k_bit_name(i), F::from_u32_unchecked(bit));
        }
    }

    fn resolved_rd_write(cs: &BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>) -> u32 {
        let low = read_field(cs, "rd/mem write write_value[0]").as_u32_reduced();
        let high = read_field(cs, "rd/mem write write_value[1]").as_u32_reduced();
        low | (high << 16)
    }

    fn run_two_field_cycle(
        opcode: u32,
        rs1_value: u32,
        rs2_value: u32,
        rd_old_value: u32,
        rd_value: u32,
    ) -> (bool, u32) {
        with_two_field_cs(opcode, rs1_value, rs2_value, rd_old_value, rd_value, |cs| {
            let satisfied = cs.is_satisfied();
            let out = resolved_rd_write(cs);
            (satisfied, out)
        })
    }

    #[test]
    fn test_mulmod_proth120() {
        let rr = ((1u64 << 32) % BB_P as u64) as u32; // R mod p (Montgomery repr neighbour)
        let vectors: [(u32, u32); 5] = [
            (rr, rr),             // x=y=R  ⇒ mont(R,R) = R
            (BB_P - 1, BB_P - 1), // x=y=p−1
            (1, 1),               // x=y=1  ⇒ R⁻¹ mod p
            (u32::MAX, u32::MAX), // raw, needs input pre-reduction
            (0, 0),               // x=y=0  ⇒ 0
        ];
        for (rs1, rs2) in vectors {
            let expected = expected_mulmod(rs1, rs2);
            let (sat, out) =
                run_two_field_cycle(encode_mop(MULMOD_FUNCT7, 10, 11, 12), rs1, rs2, 0, expected);
            assert!(sat, "mulmod circuit unsatisfied for rs1={rs1} rs2={rs2}");
            assert_eq!(
                out, expected,
                "mulmod rd must equal native BabyBear Montgomery product for rs1={rs1} rs2={rs2}"
            );
        }
    }

    #[test]
    fn test_fmamod_proth120() {
        let rr = ((1u64 << 32) % BB_P as u64) as u32;
        let vectors: [(u32, u32, u32); 4] = [
            (rr, rr, rr),                   // fma(R,R,R) = 2R mod p
            (u32::MAX, u32::MAX, u32::MAX), // raw extremes
            (1, 1, 0),                      // R⁻¹ + 0
            (BB_P - 1, 2, BB_P - 1),        // generic
        ];
        for (rs1, rs2, rd_old) in vectors {
            let expected = expected_fmamod(rs1, rs2, rd_old);
            let (sat, out) = run_two_field_cycle(
                encode_mop(FMAMOD_FUNCT7, 10, 11, 12),
                rs1,
                rs2,
                rd_old,
                expected,
            );
            assert!(
                sat,
                "fmamod circuit unsatisfied for rs1={rs1} rs2={rs2} rd_old={rd_old}"
            );
            assert_eq!(
                out, expected,
                "fmamod rd must equal native BabyBear Montgomery FMA for rs1={rs1} rs2={rs2} rd_old={rd_old}"
            );
        }
    }

    #[test]
    fn test_addmod_proth120() {
        // (rs1, rs2): wraparound + raw extremes + one ordinary in-range pair.
        let vectors: [(u32, u32); 4] = [
            (BB_P - 1, 1),        // p−1 + 1 ⇒ out = 0, k = 1
            (u32::MAX, u32::MAX), // raw extremes ⇒ k = 4 (33-bit dividend)
            (BB_P - 1, 2),        // single reduction ⇒ out = 1, k = 1
            (12345678, 87654321), // ordinary non-wrapping ⇒ out = sum, k = 0
        ];
        for (rs1, rs2) in vectors {
            let expected = expected_addmod(rs1, rs2);
            let (sat, out) =
                run_two_field_cycle(encode_mop(ADDMOD_FUNCT7, 10, 11, 12), rs1, rs2, 0, expected);
            assert!(sat, "addmod circuit unsatisfied for rs1={rs1} rs2={rs2}");
            assert_eq!(
                out, expected,
                "addmod rd must equal (rs1 + rs2) mod p for rs1={rs1} rs2={rs2}"
            );
        }
    }

    #[test]
    fn test_submod_proth120() {
        // (rs1, rs2): wraparound + raw extremes + zero + one ordinary in-range pair.
        let vectors: [(u32, u32); 5] = [
            (0, 1),               // 0 − 1 ⇒ out = p−1 (k = 2 by the +3p offset formula)
            (u32::MAX, 0),        // raw extreme ⇒ k = 5
            (0, u32::MAX),        // raw extreme ⇒ k = 0
            (0, 0),               // 0 − 0 ⇒ out = 0, k = 3 (the +3p offset)
            (87654321, 12345678), // ordinary non-wrapping ⇒ out = diff, k = 3
        ];
        for (rs1, rs2) in vectors {
            let expected = expected_submod(rs1, rs2);
            let (sat, out) =
                run_two_field_cycle(encode_mop(SUBMOD_FUNCT7, 10, 11, 12), rs1, rs2, 0, expected);
            assert!(sat, "submod circuit unsatisfied for rs1={rs1} rs2={rs2}");
            assert_eq!(
                out, expected,
                "submod rd must equal (rs1 − rs2) mod p for rs1={rs1} rs2={rs2}"
            );
        }
    }

    /// mop.rr with NON-CANONICAL operands (raw reprs ≥ p, ≤ u32::MAX). A register may hold a
    /// non-reduced BabyBear encoding; the circuit must pre-reduce the inputs and still emit a
    /// canonically-reduced output. Exercises the range budgets the asserts in
    /// `add_sub_lui_auipc_mop.rs` guarantee: the mul/fma quotient q̂ ∈ [0, 8·2^32) and the
    /// add/sub reduction count k ∈ [0,8). Covers add/mul/fma with `non_canonical()` inputs and —
    /// the worst-borrow submod case — subtraction of the largest non-canonical word from zero.
    #[test]
    fn test_mop_noncanonical_inputs_proth120() {
        // reduced operands (< p); their +p reprs are non-canonical but denote the same elements.
        let a = non_canonical(7);
        let b = non_canonical(BB_P - 3);
        let c = non_canonical(123456);

        // mulmod: both operands non-canonical.
        let expected = expected_mulmod(a, b);
        let (sat, out) =
            run_two_field_cycle(encode_mop(MULMOD_FUNCT7, 10, 11, 12), a, b, 0, expected);
        assert!(sat, "mulmod unsatisfied for non-canonical rs1={a} rs2={b}");
        assert_eq!(
            out, expected,
            "mulmod non-canonical output must match reduced product"
        );
        assert!(
            out < BB_P,
            "mulmod output must be canonical (< p), got {out}"
        );

        // addmod: both operands non-canonical (dividend up to ~4p).
        let expected = expected_addmod(a, b);
        let (sat, out) =
            run_two_field_cycle(encode_mop(ADDMOD_FUNCT7, 10, 11, 12), a, b, 0, expected);
        assert!(sat, "addmod unsatisfied for non-canonical rs1={a} rs2={b}");
        assert_eq!(
            out, expected,
            "addmod non-canonical output must match reduced sum"
        );
        assert!(
            out < BB_P,
            "addmod output must be canonical (< p), got {out}"
        );

        // fmamod: all three operands (including the rd_old addend) non-canonical.
        let expected = expected_fmamod(a, b, c);
        let (sat, out) =
            run_two_field_cycle(encode_mop(FMAMOD_FUNCT7, 10, 11, 12), a, b, c, expected);
        assert!(
            sat,
            "fmamod unsatisfied for non-canonical rs1={a} rs2={b} rd_old={c}"
        );
        assert_eq!(
            out, expected,
            "fmamod non-canonical output must match reduced fma"
        );
        assert!(
            out < BB_P,
            "fmamod output must be canonical (< p), got {out}"
        );

        // submod: subtract the maximal non-canonical word from zero (0 − u32::MAX). This is the
        // worst borrow the +3p offset must absorb (the `u32::MAX < 3p` assert covers it).
        let (rs1, rs2) = (0u32, u32::MAX);
        let expected = expected_submod(rs1, rs2);
        let (sat, out) =
            run_two_field_cycle(encode_mop(SUBMOD_FUNCT7, 10, 11, 12), rs1, rs2, 0, expected);
        assert!(
            sat,
            "submod unsatisfied for 0 − u32::MAX (max non-canonical subtrahend)"
        );
        assert_eq!(out, expected, "submod(0, u32::MAX) must reduce canonically");
        assert!(
            out < BB_P,
            "submod output must be canonical (< p), got {out}"
        );
    }

    #[test]
    fn test_plain_add_row_two_field() {
        let vectors: [(u32, u32); 3] = [
            (100, 50),     // ordinary
            (u32::MAX, 1), // wraps mod 2^32 ⇒ 0
            (0x1234_5678, 0x8765_4321),
        ];
        for (rs1, rs2) in vectors {
            let expected = rs1.wrapping_add(rs2);
            // `encode_add` takes register indices (x10, x11 → x12); the register VALUES are
            // supplied separately to the harness.
            let (sat, out) = run_two_field_cycle(encode_add(10, 11, 12), rs1, rs2, 0, expected);
            assert!(sat, "plain ADD circuit unsatisfied for rs1={rs1} rs2={rs2}");
            assert_eq!(
                out, expected,
                "plain ADD rd must equal wrapping sum for rs1={rs1} rs2={rs2}"
            );
        }
    }

    fn write_modular_row_out(
        cs: &mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>,
        out: u32,
    ) {
        let p = BB_P;
        let (z, borrow) = out.overflowing_sub(p); // z = out − p (mod 2^32); borrow = (out < p)
        let ic = ((out & 0xFFFF) < (p & 0xFFFF)) as u32; // low 16-bit limb borrow
        write_field(
            cs,
            "rd/mem write write_value[0]",
            F::from_u32_unchecked(out & 0xFFFF),
        );
        write_field(
            cs,
            "rd/mem write write_value[1]",
            F::from_u32_unchecked(out >> 16),
        );
        write_field(
            cs,
            "shared F1/F2 intermediate reg[0]",
            F::from_u32_unchecked(z & 0xFFFF),
        );
        write_field(
            cs,
            "shared F1/F2 intermediate reg[1]",
            F::from_u32_unchecked(z >> 16),
        );
        write_field(cs, "shared scratch bool[1]", F::from_u32_unchecked(ic));
        write_field(
            cs,
            "shared scratch bool[0]",
            F::from_u32_unchecked(borrow as u32),
        );
    }

    #[test]
    fn write_modular_row_out_reproduces_honest_scratch() {
        let (rs1, rs2) = (BB_P - 1, 2);
        let expected = expected_addmod(rs1, rs2); // honest out = 1, k = 1
        with_two_field_cs(
            encode_mop(ADDMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered addmod twin must be satisfied"
                );

                let out = resolved_rd_write(cs);
                // Rewrite `out` (and its implied scratch) through the helper with the SAME honest value.
                write_modular_row_out(cs, out);
                assert!(
                    cs.is_satisfied(),
                    "write_modular_row_out with the honest out must reproduce the witness scratch \
                     (z, ic, carry) and leave the row satisfied"
                );
            },
        );
    }

    #[test]
    fn mulmod_mul_relation_isolated_by_q_lo16_forgery() {
        let (rs1, rs2) = (BB_P - 1, BB_P - 1);
        let expected = expected_mulmod(rs1, rs2);
        with_two_field_cs(
            encode_mop(MULMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered mulmod twin must be satisfied"
                );

                let mut q_lo16 = read_field(cs, "shared scratch var[0]");
                Field::add_assign(&mut q_lo16, &F::ONE); // q̂ += 1, no compensating m
                write_field(cs, "shared scratch var[0]", q_lo16);

                assert!(
                    !cs.is_satisfied(),
                    "forged q_lo16 (no compensation) must break the two-field mul relation C1"
                );
            },
        );
    }

    #[test]
    fn mulmod_noncanonical_output_rejected_by_normalization() {
        let (rs1, rs2) = (u32::MAX, u32::MAX);
        let expected = expected_mulmod(rs1, rs2);
        with_two_field_cs(
            encode_mop(MULMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered mulmod twin must be satisfied"
                );

                let k = read_k_bits(cs);
                assert!(k >= 1, "need honest k ≥ 1 to form q' = q − R; got k = {k}");
                assert_eq!(
                    read_field(cs, "shared scratch bool[0]").as_u32_reduced(),
                    1,
                    "honest mulmod carry (out<p borrow) must be 1 before the forgery"
                );

                let m = read_field(cs, "MULMOD intermediate value").as_u32_reduced();
                let out_noncanon = m + BB_P; // m + p < 2p < 2^32

                // m' = m + p (field)
                let mut m_new = read_field(cs, "MULMOD intermediate value");
                Field::add_assign(&mut m_new, &F::from_u32_with_reduction(BB_P));
                write_field(cs, "MULMOD intermediate value", m_new);
                // q' = q − R keeps C1 satisfied
                write_k_bits(cs, k - 1);
                // out' = m + p with a consistent borrow-subtraction scratch ⇒ carry 1→0 (out ≥ p)
                write_modular_row_out(cs, out_noncanon);

                assert!(
                    !cs.is_satisfied(),
                    "relation-consistent non-canonical mulmod output (m+p) must be rejected by out<p normalization C5"
                );
            },
        );
    }

    #[test]
    fn mulmod_inrange_qshift_uniqueness_caught_by_link() {
        let (rs1, rs2) = (u32::MAX, u32::MAX);
        let expected = expected_mulmod(rs1, rs2);
        with_two_field_cs(
            encode_mop(MULMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered mulmod twin must be satisfied"
                );

                let k = read_k_bits(cs);
                assert!(
                    k <= 6,
                    "need k ≤ 6 to form q' = q + R in three bits; got k = {k}"
                );

                let mut m_new = read_field(cs, "MULMOD intermediate value");
                Field::sub_assign(&mut m_new, &F::from_u32_with_reduction(BB_P)); // m − p (field wrap to ~char)
                write_field(cs, "MULMOD intermediate value", m_new);
                write_k_bits(cs, k + 1); // q' = q + R (still in-range)

                assert!(
                    !cs.is_satisfied(),
                    "in-range q+R / m−p shift must be rejected by the link (out cannot equal the wrapped m')"
                );
            },
        );
    }

    #[test]
    fn mulmod_output_off_by_one_rejected_by_link() {
        let (rs1, rs2) = (BB_P - 1, BB_P - 1);
        let expected = expected_mulmod(rs1, rs2);
        with_two_field_cs(
            encode_mop(MULMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered mulmod twin must be satisfied"
                );

                let m = read_field(cs, "MULMOD intermediate value").as_u32_reduced();
                // Keep out' in [0, p) so ONLY the link fires (out ≥ p would also trip normalization).
                let out_off = if m + 1 < BB_P { m + 1 } else { m - 1 };
                write_modular_row_out(cs, out_off);

                assert!(
                    !cs.is_satisfied(),
                    "off-by-one mulmod output must be rejected by the out↔residue link C4"
                );
            },
        );
    }

    #[test]
    fn addmod_output_off_by_one_rejected_by_add_relation() {
        let (rs1, rs2) = (BB_P - 1, 2);
        let expected = expected_addmod(rs1, rs2); // = 1, k = 1
        with_two_field_cs(
            encode_mop(ADDMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered addmod twin must be satisfied"
                );

                let out = resolved_rd_write(cs);
                assert!(
                    out + 1 < BB_P,
                    "need out + 1 < p to keep ONLY the add relation firing"
                );
                write_modular_row_out(cs, out + 1);

                assert!(
                    !cs.is_satisfied(),
                    "off-by-one addmod output must be rejected by the add relation C4 (x + y − k·p̂ − out)·is_addmod"
                );
            },
        );
    }

    #[test]
    fn submod_output_off_by_one_rejected_by_sub_relation() {
        let (rs1, rs2) = (87654321u32, 12345678u32);
        let expected = expected_submod(rs1, rs2); // = 75308643, k = 3
        with_two_field_cs(
            encode_mop(SUBMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered submod twin must be satisfied"
                );

                let out = resolved_rd_write(cs);
                assert!(
                    out + 1 < BB_P,
                    "need out + 1 < p to keep ONLY the sub relation firing"
                );
                write_modular_row_out(cs, out + 1);

                assert!(
                    !cs.is_satisfied(),
                    "off-by-one submod output must be rejected by the sub relation C4 (x − y + 3p̂ − k·p̂ − out)·is_submod"
                );
            },
        );
    }

    #[test]
    fn addmod_kshift_noncanonical_output_rejected_by_normalization() {
        let (rs1, rs2) = (BB_P - 1, 1);
        let expected = expected_addmod(rs1, rs2); // = 0, honest k = 1
        with_two_field_cs(
            encode_mop(ADDMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered addmod twin must be satisfied"
                );

                let k = read_k_bits(cs);
                assert!(k >= 1, "need honest k ≥ 1 for the k−1 shift; got k = {k}");
                assert_eq!(
                    read_field(cs, "shared scratch bool[0]").as_u32_reduced(),
                    1,
                    "honest addmod carry (out<p borrow) must be 1 before the forgery"
                );

                let out = resolved_rd_write(cs);
                write_k_bits(cs, k - 1); // under-count the reduction
                write_modular_row_out(cs, out + BB_P); // out + p ≥ p ⇒ carry 1→0

                assert!(
                    !cs.is_satisfied(),
                    "k−1 / out+p addmod forgery must be rejected by out<p normalization C5"
                );
            },
        );
    }

    #[test]
    fn out_of_range_q_invisible_to_arithmetic_checks() {
        let (rs1, rs2) = (BB_P - 1, BB_P - 1);
        let expected = expected_mulmod(rs1, rs2);
        with_two_field_cs(
            encode_mop(MULMOD_FUNCT7, 10, 11, 12),
            rs1,
            rs2,
            0,
            expected,
            |cs| {
                assert!(
                    cs.is_satisfied(),
                    "untampered mulmod twin must be satisfied"
                );

                // Honest-witness sanity so a wrong vector/name fails loudly (k = 1, t = (1,0,0)).
                assert_eq!(
                    read_field(cs, "shared scratch var[1]").as_u32_reduced(),
                    0,
                    "honest q_hi16 must be 0 for the (p−1, p−1) vector"
                );
                assert_eq!(
                    read_field(cs, "shared scratch bool[4]").as_u32_reduced(),
                    0,
                    "honest t2 must be 0 for the (p−1, p−1) vector"
                );

                // q_hi16 += 2^19  ⇒  q_hi16 = 2^19 ≥ 2^16 (out of RC-16 range).
                let mut q_hi16 = read_field(cs, "shared scratch var[1]");
                Field::add_assign(&mut q_hi16, &F::from_u32_unchecked(1 << 19));
                write_field(cs, "shared scratch var[1]", q_hi16);
                // t2 -= 2  ⇒  t2 = −2 (non-Boolean); Δq̂ = 2^35 − 2^35 = 0 keeps C1 satisfied.
                let mut t2 = read_field(cs, "shared scratch bool[4]");
                Field::sub_assign(&mut t2, &F::from_u32_with_reduction(2));
                write_field(cs, "shared scratch bool[4]", t2);

                assert!(
                    cs.is_satisfied(),
                    "an out-of-range q_hi16 + non-Boolean t2 with Δq̂ = 0 must be INVISIBLE to the \
                     arithmetic constraints — only the RC-16 / Booleanity LOOKUPS (not evaluated at the \
                     single-cycle level) can reject it"
                );
            },
        );
    }

    const TRI_ADD_FUNCT7: u32 = 0x61;

    #[test]
    fn test_tri_add_proth120() {
        let vectors: [(u32, u32, u32); 4] = [
            (100, 50, 25),                           // no carries
            (u32::MAX, 1, 0),                        // low+high carry chain (wrap to 0)
            (u32::MAX, u32::MAX, u32::MAX),          // each limb carry hits 2
            (0x1234_5678, 0x8765_4321, 0xFFFF_FFFF), // mixed
        ];
        for (rs1, rs2, rd_old) in vectors {
            let expected = rs1.wrapping_add(rs2).wrapping_add(rd_old);
            let (sat, out) = run_two_field_cycle(
                encode_mop(TRI_ADD_FUNCT7, 10, 11, 12),
                rs1,
                rs2,
                rd_old,
                expected,
            );
            assert!(
                sat,
                "tri-add circuit unsatisfied for rs1={rs1} rs2={rs2} rd_old={rd_old}"
            );
            assert_eq!(
                out, expected,
                "tri-add rd must equal wrapping rs1+rs2+rd_old for rs1={rs1} rs2={rs2} rd_old={rd_old}"
            );
        }
    }
}
