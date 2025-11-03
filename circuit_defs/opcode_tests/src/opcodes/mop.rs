use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;

/// Format: funct7[31:25] | rs2[24:20] | rs1[19:15] | funct3[14:12] | rd[11:7] | opcode[6:0]
fn make_instruction_from_parts_for_mop(funct7: u8, rs2: u8, rs1: u8, funct3: u8, rd: u8) -> u32 {
    const OPCODE_SYSTEM: u32 = 0x73;
    ((funct7 as u32) << 25)
        | ((rs2 as u32) << 20)
        | ((rs1 as u32) << 15)
        | ((funct3 as u32) << 12)
        | ((rd as u32) << 7)
        | OPCODE_SYSTEM
}

#[test]
fn test_mop_addmod() {
    // ADDMOD: (a + b) mod (2^31 - 1)
    const FUNCT7_ADDMOD: u8 = 0b1000001;
    const FUNCT3_MOP: u8 = 0b100;
    let instr = make_instruction_from_parts_for_mop(FUNCT7_ADDMOD, 2, 1, FUNCT3_MOP, 3);

    // Simple addition without overflow
    let mut regs = [0; 32];
    regs[1] = 100;
    regs[2] = 50;
    test_single_mop("addmod x3, x1, x2", Some(instr), regs, Some((3, 150)));

    // Addition with overflow
    let mut regs = [0; 32];
    regs[1] = 0xFFFFFFFF;
    regs[2] = 1;
    test_single_mop(
        "addmod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2)), // 2^32 mod (2^31 - 1) = 2
    );

    // Large numbers (2^31 + 2^31)
    let mut regs = [0; 32];
    regs[1] = 0x80000000;
    regs[2] = 0x80000000;
    test_single_mop(
        "addmod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2)), // 2^32 mod (2^31 - 1) = 2
    );
}

#[test]
fn test_mop_submod() {
    // (a - b) mod (2^31 - 1)
    const FUNCT7_SUBMOD: u8 = 0b1000011;
    const FUNCT3_MOP: u8 = 0b100;

    let instr = make_instruction_from_parts_for_mop(FUNCT7_SUBMOD, 2, 1, FUNCT3_MOP, 3);

    // Simple subtraction
    let mut regs = [0; 32];
    regs[1] = 100;
    regs[2] = 50;
    test_single_mop("submod x3, x1, x2", Some(instr), regs, Some((3, 50)));

    // Subtraction with underflow
    let mut regs = [0; 32];
    regs[1] = 0;
    regs[2] = 1;
    test_single_mop(
        "submod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2147483646)), // -1 mod (2^31 - 1) = 2^31 - 2
    );

    // Negative result wraps
    let mut regs = [0; 32];
    regs[1] = 50;
    regs[2] = 100;
    test_single_mop(
        "submod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2147483597)), // -50 mod (2^31 - 1) = 2^31 - 51
    );
}

#[test]
fn test_mop_mulmod() {
    // (a * b) mod (2^31 - 1)
    const FUNCT7_MULMOD: u8 = 0b1000101;
    const FUNCT3_MOP: u8 = 0b100;

    let instr = make_instruction_from_parts_for_mop(FUNCT7_MULMOD, 2, 1, FUNCT3_MOP, 3);

    // Simple multiplication
    let mut regs = [0; 32];
    regs[1] = 10;
    regs[2] = 5;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 50)));

    // Multiplication with overflow (2^16 * 2^16 = 2^32)
    let mut regs = [0; 32];
    regs[1] = 0x10000;
    regs[2] = 0x10000;
    test_single_mop(
        "mulmod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2)), // 2^32 mod (2^31 - 1) = 2
    );

    // Large numbers (65535 * 65535 = 4,294,836,225)
    let mut regs = [0; 32];
    regs[1] = 0xFFFF;
    regs[2] = 0xFFFF;
    test_single_mop(
        "mulmod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2147352578)),
    );
}

#[test]
fn test_mop_addmod_edge_cases() {
    const FUNCT7_ADDMOD: u8 = 0b1000001;
    const FUNCT3_MOP: u8 = 0b100;
    const MODULUS: u32 = 2147483647; // 2^31 - 1

    let instr = make_instruction_from_parts_for_mop(FUNCT7_ADDMOD, 2, 1, FUNCT3_MOP, 3);

    // Identity: x + 0 = x
    let mut regs = [0; 32];
    regs[1] = 12345;
    regs[2] = 0;
    test_single_mop("addmod x3, x1, x2", Some(instr), regs, Some((3, 12345)));

    // Both zeros: 0 + 0 = 0
    let mut regs = [0; 32];
    regs[1] = 0;
    regs[2] = 0;
    test_single_mop("addmod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Adding modulus to itself
    let mut regs = [0; 32];
    regs[1] = MODULUS;
    regs[2] = MODULUS;
    test_single_mop("addmod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Adding 1 to modulus: (2^31-1) + 1 === 0 + 1 = 1
    let mut regs = [0; 32];
    regs[1] = MODULUS;
    regs[2] = 1;
    test_single_mop("addmod x3, x1, x2", Some(instr), regs, Some((3, 1)));
}

#[test]
fn test_mop_submod_edge_cases() {
    const FUNCT7_SUBMOD: u8 = 0b1000011;
    const FUNCT3_MOP: u8 = 0b100;
    const MODULUS: u32 = 2147483647; // 2^31 - 1

    let instr = make_instruction_from_parts_for_mop(FUNCT7_SUBMOD, 2, 1, FUNCT3_MOP, 3);

    // Identity: x - 0 = x
    let mut regs = [0; 32];
    regs[1] = 12345;
    regs[2] = 0;
    test_single_mop("submod x3, x1, x2", Some(instr), regs, Some((3, 12345)));

    // Self subtraction: x - x = 0
    let mut regs = [0; 32];
    regs[1] = 12345;
    regs[2] = 12345;
    test_single_mop("submod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Zero minus zero: 0 - 0 = 0
    let mut regs = [0; 32];
    regs[1] = 0;
    regs[2] = 0;
    test_single_mop("submod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Subtracting from modulus: (2^31-1) - 1 === 0 - 1
    let mut regs = [0; 32];
    regs[1] = MODULUS;
    regs[2] = 1;
    test_single_mop(
        "submod x3, x1, x2",
        Some(instr),
        regs,
        Some((3, 2147483646)), //  0 - 1 = -1 === 2^31 - 2
    );

    // Zero minus modulus
    let mut regs = [0; 32];
    regs[1] = 0;
    regs[2] = MODULUS;
    test_single_mop("submod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Large underflow: 1 - MAX_U32
    let mut regs = [0; 32];
    regs[1] = 1;
    regs[2] = 0xFFFFFFFF;
    test_single_mop("submod x3, x1, x2", Some(instr), regs, Some((3, 0)));
}

#[test]
fn test_mop_mulmod_edge_cases() {
    const FUNCT7_MULMOD: u8 = 0b1000101;
    const FUNCT3_MOP: u8 = 0b100;
    const MODULUS: u32 = 2147483647; // 2^31 - 1

    let instr = make_instruction_from_parts_for_mop(FUNCT7_MULMOD, 2, 1, FUNCT3_MOP, 3);

    // Multiplication by zero: x * 0 = 0
    let mut regs = [0; 32];
    regs[1] = 12345;
    regs[2] = 0;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Identity: x * 1 = x
    let mut regs = [0; 32];
    regs[1] = 12345;
    regs[2] = 1;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 12345)));

    // Zero times zero: 0 * 0 = 0
    let mut regs = [0; 32];
    regs[1] = 0;
    regs[2] = 0;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Modulus times 2: (2^31-1) * 2 === 0 * 2 = 0
    let mut regs = [0; 32];
    regs[1] = MODULUS;
    regs[2] = 2;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Modulus squared: (2^31-1)^2 === 0 * 0 = 0
    let mut regs = [0; 32];
    regs[1] = MODULUS;
    regs[2] = MODULUS;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 0)));

    // Powers of 2: 2^20 * 2^10 = 2^30
    let mut regs = [0; 32];
    regs[1] = 1 << 20;
    regs[2] = 1 << 10;
    test_single_mop("mulmod x3, x1, x2", Some(instr), regs, Some((3, 1 << 30)));
}

#[test]
fn test_mop_mixed_operations() {
    // Test different register combinations
    const FUNCT7_ADDMOD: u8 = 0b1000001;
    const FUNCT3_MOP: u8 = 0b100;

    // Using different destination registers
    let instr_rd5 = make_instruction_from_parts_for_mop(FUNCT7_ADDMOD, 2, 1, FUNCT3_MOP, 5);
    let mut regs = [0; 32];
    regs[1] = 100;
    regs[2] = 200;
    test_single_mop("addmod x5, x1, x2", Some(instr_rd5), regs, Some((5, 300)));

    // Using same source register twice (rs1 = rs2)
    let instr_same = make_instruction_from_parts_for_mop(FUNCT7_ADDMOD, 1, 1, FUNCT3_MOP, 3);
    let mut regs = [0; 32];
    regs[1] = 1000;
    test_single_mop("addmod x3, x1, x1", Some(instr_same), regs, Some((3, 2000)));

    // Source and destination overlap (rd = rs1)
    let instr_overlap = make_instruction_from_parts_for_mop(FUNCT7_ADDMOD, 2, 3, FUNCT3_MOP, 3);
    let mut regs = [0; 32];
    regs[2] = 50;
    regs[3] = 150;
    test_single_mop(
        "addmod x3, x3, x2",
        Some(instr_overlap),
        regs,
        Some((3, 200)),
    );
}

fn test_single_mop(
    _instruction: &str,
    bytecode: Option<u32>,
    initial_registers: [u32; 32],
    final_register: Option<(usize, u32)>,
) {
    use cs::cs::cs_reference::BasicAssembly;
    use cs::definitions::timestamp_from_chunk_cycle_and_sequence;
    use cs::machine::machine_configurations::create_csr_table_for_delegation;
    use cs::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
    use cs::machine::Machine;
    use cs::machine::UNIMP_OPCODE;
    use cs::tables::LookupWrapper;
    use cs::tables::TableType;
    use field::Mersenne31Field;
    use prover::tracers::main_cycle_optimized::DelegationTracingData;
    use prover::tracers::main_cycle_optimized::GPUFriendlyTracer;
    use prover::tracers::main_cycle_optimized::RamTracingData;
    use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
    use prover::VectorMemoryImplWithRom;
    use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
    use risc_v_simulator::cycle::MachineConfig;
    use risc_v_simulator::delegations::DelegationsCSRProcessor;
    use std::alloc::Global;
    use std::collections::HashMap;

    const ENTRY_POINT: u32 = 0;
    const SECOND_WORD_BITS: usize = 4;
    const MAX_CYCLES: usize = (1 << 20) - 1;
    const MAX_ROM: usize = 1 << 20;
    const MAX_RAM: usize = 1 << 24;
    const START_ROM: u32 = 0;
    const ROM_BYTECODE_PADDING: &[u32] = &[UNIMP_OPCODE; (MAX_ROM / 4) - 4];

    let bytecode = vec![bytecode.unwrap()];

    let mut state: RiscV32StateForUnrolledProver<IWithoutByteAccessIsaConfigWithDelegation> = {
        let mut state =
            RiscV32StateForUnrolledProver::<IWithoutByteAccessIsaConfigWithDelegation>::initial(
                ENTRY_POINT,
            );
        state.observable.registers = initial_registers;
        state
    };

    let mut memory_source = {
        let mut memory_source = VectorMemoryImplWithRom::new_for_byte_size(MAX_RAM, MAX_ROM);
        for (i, &instruction) in bytecode.iter().chain(ROM_BYTECODE_PADDING).enumerate() {
            memory_source.populate(START_ROM + i as u32 * 4, instruction);
        }
        memory_source
    };

    let mut tracer: GPUFriendlyTracer<IWithoutByteAccessIsaConfigWithDelegation> = {
        let delegation_factories = setups::delegation_factories_for_machine::<
            IWithoutByteAccessIsaConfigWithDelegation,
            Global,
        >();

        let ram_tracer = RamTracingData::<true>::new_for_ram_size_and_rom_bound(1 << 30, MAX_ROM);
        let delegation_tracer = DelegationTracingData {
            all_per_type_logs: HashMap::new(),
            delegation_witness_factories: delegation_factories,
            current_per_type_logs: HashMap::new(),
            num_traced_registers: 0,
            mem_reads_offset: 0,
            mem_writes_offset: 0,
        };

        let initial_ts = timestamp_from_chunk_cycle_and_sequence(0, MAX_CYCLES, 0);
        GPUFriendlyTracer::new(initial_ts, ram_tracer, delegation_tracer, MAX_CYCLES, 1)
    };

    let mut non_determinism_source = QuasiUARTSource::default();
    let mut custom_csr_processor = DelegationsCSRProcessor;

    state.cycle(
        &mut memory_source,
        &mut tracer,
        &mut non_determinism_source,
        &mut custom_csr_processor,
    );

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS,
        TableType::SpecialCSRProperties.to_table_id(),
    );

    let mut cs = {
        let oracle: MainRiscVOracle<'static, IWithoutByteAccessIsaConfigWithDelegation> = unsafe {
            std::mem::transmute(MainRiscVOracle {
                cycle_data: &tracer.trace_chunk,
            })
        };
        BasicAssembly::<Mersenne31Field>::new_with_oracle(oracle)
    };

    let (circuit_pc_prev, circuit_pc) = {
        let (state_prev, state_next) =
            MinimalMachineNoExceptionHandlingWithDelegation::run_single_cycle::<SECOND_WORD_BITS>(
                &bytecode,
                &mut cs,
                Some(LookupWrapper::Dimensional3(csr_table)),
            );
        let pc_prev = state_prev.pc.get_value_unsigned(&cs).unwrap();
        let pc_next = state_next.pc.get_value_unsigned(&cs).unwrap();
        (pc_prev, pc_next)
    };

    let circuit_registers = {
        let mut registers = [0; 32];
        for query in &cs.shuffle_ram_queries {
            if let Some(id) = query.query_type.get_register_id(&cs) {
                registers[id as usize] = query.get_write_value(&cs);
            }
        }
        registers
    };

    assert_eq!(
        (ENTRY_POINT, state.observable.pc),
        (circuit_pc_prev, circuit_pc)
    );
    assert_eq!(state.observable.registers, circuit_registers);

    if let Some((id, val)) = final_register {
        assert_eq!(circuit_registers[id], val);
    }
}
