#![expect(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(let_chains)]
#![feature(allocator_api)]

// NOTE: Temporary disabled due to conflicts with witness evaluation

// run them all with: cargo test --profile test-release --lib --package opcode_tests
#[cfg(test)]
mod opcodes {
    mod add;
    mod addi;
    mod auipc;
    mod beq;
    mod jal;
    mod jalr;
    mod lb;
    mod lui;
    mod sb;
    // the rest are just same format
    mod and;
    mod andi;
    mod bge;
    mod bgeu;
    mod blt;
    mod bltu;
    mod bne;
    mod div;
    mod divu;
    // mod fence;
    mod lbu;
    mod lh;
    mod lhu;
    mod lw;
    // mod misalign_jalr;
    mod mul;
    mod mulh;
    mod mulhsu;
    mod mulhu;
    mod or;
    mod ori;
    mod rem;
    mod remu;
    mod sh;
    mod sll;
    mod slli;
    mod slt;
    mod slti;
    mod sltiu;
    mod sltu;
    mod sra;
    mod srai;
    mod srl;
    mod srli;
    mod sub;
    mod sw;
    mod xor;
    mod xori;
    // just for delegation
    mod csrrw;
}

use cs::cs::cs_reference::BasicAssembly;
use cs::machine::machine_configurations::create_csr_table_for_delegation;
use cs::machine::machine_configurations::full_isa_with_delegation_no_exceptions::FullIsaMachineWithDelegationNoExceptionHandling;
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
use risc_v_simulator::abstractions::tracer::Tracer;
use risc_v_simulator::cycle::state::RiscV32State;
use risc_v_simulator::cycle::state::NUM_REGISTERS;
use risc_v_simulator::cycle::IMStandardIsaConfig;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::delegations::DelegationsCSRProcessor;
use risc_v_simulator::mmu::NoMMU;
use std::alloc::Global;
use std::collections::HashMap;

const ENTRY_POINT: u32 = 0;
const SECOND_WORD_BITS: usize = 4;

#[test]
fn mario_test() {
    test_single_opcode("addi x1,x0,1", None, [0; 32], Some((1, 1)));
    // test_single_opcode("addi x1,x0,1", [0;32], (1,1));
    // test_single_opcode("add, x24, x4, x24", [0;32], (1,0));
    // test_single_opcode("beq x19, x19, 1024", [0;32], (1,0));
    // test_single_opcode("beq, x10, x11, 1366", [0;32], Some((10,5)));
    // test_single_opcode("jalr, x25, 64(x4)", [0;32], None);
    //              test_single_opcode("lb, x20, -8(x12)", {let mut xs=[0;32]; xs[12]=1024; xs}, None);
    // test_single_opcode("lb, x20, 0(x12)", {let mut xs=[0;32]; xs[12]=512; xs}, None);
    // test_single_opcode("lb, x20, 0(x12)", {let mut xs=[0;32]; xs[12]=1<<5; xs}, None);
    // test_single_opcode("lb, x20, 399(x12)", {let mut xs=[0;32]; xs[12]=1<<20; xs}, None);
    // test_single_opcode("sb, x11, 512(x29)", {let mut xs=[0;32]; xs[11]=2147483647; xs[29]=2097152; xs}, None);
    // test_single_opcode(" lui x8, 0", [0; 32], None);
    // test_single_opcode("lb, x11, 256(x21)", {let mut xs = [0; 32]; xs[21]=2048; xs}, None);
    // test_single_opcode("div, x3, x1, x2", None, {let mut xs = [0; 32]; xs[1]=i32::MIN as u32; xs[2]=-1_i32 as u32; xs}, Some((3, i32::MIN as u32)));
    // test_single_opcode("divu, x3, x1, x2", None, {let mut xs = [0; 32]; xs[1]=i32::MIN as u32; xs[2]=-1_i32 as u32; xs}, Some((3, 0)));
    // test_single_opcode("rem, x3, x1, x2", None, {let mut xs = [0; 32]; xs[1]=i32::MIN as u32; xs[2]=-1_i32 as u32; xs}, Some((3, 0)));
    // test_single_opcode("remu, x3, x1, x2", None, {let mut xs = [0; 32]; xs[1]=i32::MIN as u32; xs[2]=-1_i32 as u32; xs}, Some((3, i32::MIN as u32)));
    // const WHATEVER: u32 = 0x7c5150f3; // 1985 1987 1988 1989
    // crate::test_single_opcode("csrrwi x1, whatever, 2", Some(WHATEVER), [0;32], None);
}

#[test]
fn broken_tests() {
    fn broken_test_impl(
        instruction: &str,
        alternative_instruction_bytecode: Option<u32>,
        initial_registers: [u32; NUM_REGISTERS],
        final_register: Option<(usize, u32)>,
    ) {
        assert!(alternative_instruction_bytecode.is_some() && final_register.is_none());
        assert!(std::panic::catch_unwind(|| test_single_opcode(
            instruction,
            alternative_instruction_bytecode,
            initial_registers,
            final_register
        ))
        .unwrap_err()
        .downcast_ref::<String>()
        .unwrap()
        .starts_with("unsatisfied"));
    }

    // opcodes that we don't support
    const FENCE_OPCODE: u32 = 0x140000f;
    const ECALL_OPCODE: u32 = 0x73;
    const EBREAK_OPCODE: u32 = 0x100073;
    const CSRRW_UNSUPPORTED_OPCODE: u32 = UNIMP_OPCODE;
    const CSRRS_OPCODE: u32 = 0x112073;
    const CSRRC_OPCODE: u32 = 0x113073;
    const CSRRWI_OPCODE: u32 = 0x115073;
    const CSRRSI_OPCODE: u32 = 0x116073;
    const CSRRCI_OPCODE: u32 = 0x117073;
    const FADDS_OPCODE: u32 = 0x2081d3;
    broken_test_impl("fence w, r", Some(FENCE_OPCODE), [0; 32], None);
    broken_test_impl("fence w, r", Some(FENCE_OPCODE), [0; 32], None);
    broken_test_impl("ecall", Some(ECALL_OPCODE), [0; 32], None);
    broken_test_impl("ebreak", Some(EBREAK_OPCODE), [0; 32], None);
    broken_test_impl(
        "csrrw x0, 3072, x0",
        Some(CSRRW_UNSUPPORTED_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl("csrrs x0, 1, x2", Some(CSRRS_OPCODE), [0; 32], None);
    broken_test_impl("csrrc x0, 1, x2", Some(CSRRC_OPCODE), [0; 32], None);
    broken_test_impl("csrrwi x0, 1, 2", Some(CSRRWI_OPCODE), [0; 32], None);
    broken_test_impl("csrrsi x0, 1, 2", Some(CSRRSI_OPCODE), [0; 32], None);
    broken_test_impl("csrrci x0, 1, 2", Some(CSRRCI_OPCODE), [0; 32], None);
    broken_test_impl("fadd.s x3,x1,x2", Some(FADDS_OPCODE), [0; 32], None);

    // csrrw for unsupported delegations
    const CSRRW_BLAKE2_OPCODE: u32 = 0x7c1110f3; // 1985
    const CSRRW_BLAKE2ROUNDXOR_OPCODE: u32 = 0x7c3110f3; // 1987
    const CSRRW_BLAKE2ROUNDREG_OPCODE: u32 = 0x7c4110f3; // 1988
    const CSRRW_MERSENNEEXT4_OPCODE: u32 = 0x7c5110f3; // 1989
    const CSRRW_MERSENNEEXT4INDIRECT_OPCODE: u32 = 0x7c8110f3; // 1992
    const CSRRW_POSEIDON2_OPCODE: u32 = 0x7c6110f3; // 1990
    broken_test_impl(
        "csrrw x0, 1985, x0",
        Some(CSRRW_BLAKE2_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrw x0, 1987, x0",
        Some(CSRRW_BLAKE2ROUNDXOR_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrw x0, 1988, x0",
        Some(CSRRW_BLAKE2ROUNDREG_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrw x0, 1989, x0",
        Some(CSRRW_MERSENNEEXT4_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrw x0, 1988, x0",
        Some(CSRRW_MERSENNEEXT4INDIRECT_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrw x0, 1989, x0",
        Some(CSRRW_POSEIDON2_OPCODE),
        [0; 32],
        None,
    );

    // csrrw for supported delegations
    const CSRRWI_NONDETERMINISM_OPCODE: u32 = 0x7c0150f3; // 1984
    const CSRRWI_BLAKE2ROUNDEXTENDED_OPCODE: u32 = 0x7c7150f3; // 1991
    const CSRRWI_U256BIGINTOPS_OPCODE: u32 = 0x7ca150f3; // 1994
    broken_test_impl(
        "csrrwi x1, 1984, 2",
        Some(CSRRWI_NONDETERMINISM_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrwi x1, 1991, 2",
        Some(CSRRWI_BLAKE2ROUNDEXTENDED_OPCODE),
        [0; 32],
        None,
    );
    broken_test_impl(
        "csrrwi x1, 1994, 2",
        Some(CSRRWI_U256BIGINTOPS_OPCODE),
        [0; 32],
        None,
    );
}

/// 1. simulate
/// 2. resolve circuit
/// 3. check they're same
pub fn test_single_opcode(
    instruction: &str,
    alternative_instruction_bytecode: Option<u32>,
    initial_registers: [u32; NUM_REGISTERS],
    final_register: Option<(usize, u32)>,
) {
    dbg!(instruction);
    let bytecode = if let Some(b) = alternative_instruction_bytecode {
        vec![b]
    } else {
        lib_rv32_asm::assemble_program(instruction).unwrap()
    };

    const MAX_CYCLES: usize = (1 << 20) - 1;
    const MAX_ROM: usize = 1 << 20; // should be this bc we have lookup table
    const MAX_RAM: usize = 1 << 24;
    const START_ROM: u32 = 0;
    const ROM_BYTECODE_PADDING: &[u32] = &[UNIMP_OPCODE; (MAX_ROM / 4) - 4]; // necessary for ROM lookup table
    let mut state: RiscV32State<IMStandardIsaConfig> = {
        let mut state = RiscV32State::<IMStandardIsaConfig>::initial(ENTRY_POINT);
        state.registers = initial_registers;
        state
    };
    let mut memory_source = {
        let mut memory_source = VectorMemoryImplWithRom::new_for_byte_size(MAX_RAM, MAX_ROM); // use full RAM
        for (i, &instruction) in bytecode.iter().chain(ROM_BYTECODE_PADDING).enumerate() {
            memory_source.populate(START_ROM + i as u32 * 4, instruction);
        }
        memory_source
    };
    let mut tracer: GPUFriendlyTracer<IMStandardIsaConfig> = {
        let delegation_factories =
            setups::delegation_factories_for_machine::<IMStandardIsaConfig, Global>();

        let ram_tracer = RamTracingData::new_for_ram_size_and_rom_bound(1 << 30, MAX_ROM); // use 1 GB RAM
        let delegation_tracer = DelegationTracingData {
            all_per_type_logs: HashMap::new(),
            delegation_witness_factories: delegation_factories,
            current_per_type_logs: HashMap::new(),
            num_traced_registers: 0,
            mem_reads_offset: 0,
            mem_writes_offset: 0,
        };

        let aux_data = (0, ram_tracer, delegation_tracer);

        let tracer = GPUFriendlyTracer::create_from_initial_state_for_num_cycles_and_chunk_size(
            &state, aux_data, MAX_CYCLES, MAX_CYCLES,
        );

        tracer
    };
    let mut mmu = NoMMU { sapt: state.sapt };
    let mut non_determinism_source = QuasiUARTSource::default();
    let mut custom_csr_processor = DelegationsCSRProcessor;
    let simulator_crashed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        state.cycle_ext(
            &mut memory_source,
            &mut tracer,
            &mut mmu,
            &mut non_determinism_source,
            &mut custom_csr_processor,
        )
    }))
    .is_err();
    if simulator_crashed {
        let instr = bytecode[0];
        let opcode = instr & 0b0111_1111;
        let f3 = (instr >> 12) & 0b111;
        let f7 = instr >> 25;
        let rd_index = (instr >> 7) & 0b1_1111;
        if state.pc == 0 {
            // correct?
            state.pc = 4;
        }
        // take from state
        let rs1 =
            state.get_first_register(risc_v_simulator::utils::get_formal_rs1(instr), &mut tracer);
        let rs2 =
            state.get_second_register(risc_v_simulator::utils::get_formal_rs2(instr), &mut tracer);

        let mut set_dummy_witness = || state.set_register(0, 0, &mut tracer);

        // dummy is necessary sometimes to avoid circuit from crashing during memory opcode
        // even though we normally have no witness where we put the dummy

        match opcode {
            // JAL misaligned
            0b1101111 => state.set_register(rd_index, 4, &mut tracer),
            // JALR misaligned
            0b1100111 => state.set_register(rd_index, 4, &mut tracer),
            // BRANCH misaligned
            0b1100011 => (),
            // LOADS misaligned - write to rd
            0b0000011 if f3 != 0b000 => set_dummy_witness(),
            // STORES misaligned - write to mem
            0b0100011 if f3 != 0b000 => set_dummy_witness(),
            // ECALL / EBREAK
            0b1110011 if f3 == 0b000 => (),
            // CSR ops - since we crashed it's not non-determinism and it's not supported delegation. we're forced to use dummy reg write but this is wrong
            // WARNING: currently simulator also crashes for supported csr if we don't use abi correctly, and we are patching those too!
            0b1110011 if f3 != 0b000 => set_dummy_witness(),
            // FENCE
            0b0001111 => (),
            // FADD.S
            0b1010011 if f7 == 0b0000000 => {
                state.set_register(rd_index, (rs1 as f32 + rs2 as f32) as u32, &mut tracer)
            }
            _ => unreachable!("{instr:x}"),
        }
    }

    assert!(cs::cs::cs_reference::RESOLVE_WITNESS); // don't wanna deal with this problem again
    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        IMStandardIsaConfig::ALLOWED_DELEGATION_CSRS,
        TableType::SpecialCSRProperties.to_table_id(),
    );
    let mut cs = {
        let oracle: MainRiscVOracle<'static, IMStandardIsaConfig> = unsafe {
            std::mem::transmute(MainRiscVOracle {
                cycle_data: &tracer.trace_chunk,
            })
        };
        BasicAssembly::<Mersenne31Field>::new_with_oracle(oracle)
    };
    let (circuit_pc_prev, circuit_pc) = {
        let (state_prev, state_next) =
            FullIsaMachineWithDelegationNoExceptionHandling::run_single_cycle::<SECOND_WORD_BITS>(
                &bytecode,
                &mut cs,
                Some(LookupWrapper::Dimensional3(csr_table)),
            );
        let pc_prev = state_prev.pc.get_value_unsigned(&cs).unwrap();
        let pc_next = state_next.pc.get_value_unsigned(&cs).unwrap();
        (pc_prev, pc_next)
    };
    let (circuit_registers, circuit_mem_accesses) = {
        let mut registers = [0; NUM_REGISTERS];
        let mut circuit_mem_accesses = vec![];
        for query in &cs.shuffle_ram_queries {
            if let Some(id) = query.query_type.get_register_id(&cs) {
                registers[id as usize] = query.get_write_value(&cs);
            } else if let Some(addr) = query.query_type.get_address(&cs) {
                if query.is_readonly() {
                    // dbg!(('R',addr, query.get_read_value(&cs)));
                    circuit_mem_accesses.push((addr, query.get_read_value(&cs)));
                } else {
                    // dbg!(('W',addr, query.get_write_value(&cs)));
                    circuit_mem_accesses.push((addr, query.get_write_value(&cs)));
                }
            } else {
                unreachable!();
            }
        }
        (registers, circuit_mem_accesses)
    };

    // really the only conditions we need
    assert_eq!((ENTRY_POINT, state.pc), (circuit_pc_prev, circuit_pc));
    assert!(
        state.registers == circuit_registers,
        "expected final register state\n\t{:?}\nbut circuit witness produced\n\t{:?}",
        state.registers,
        circuit_registers,
    );

    // check return value
    if let Some((id, val)) = final_register {
        // more of a pedantic detail
        assert_eq!(circuit_registers[id], val);
    }

    // check ram reads/writes (does not apply to rom)
    // TODO: might need to adjust this for reads that were overwritten
    // dbg!(tracer.ram_tracer.accesses_per_cycles[0]);
    for (addr, val) in circuit_mem_accesses {
        assert_eq!(val, memory_source.ram[addr as usize / 4]);
    }
}

#[allow(dead_code)]
trait TestCase {
    const TESTCASES: &str;
    const MATCH: &str;
    const PATCH_MATCH: Option<&str>;
    const OPFIELDS: &[usize];
    const PATCH_IMMEDIATE: Option<usize>;
    const PATCH_IMMEDIATE_WITH_REGISTER: bool;
    const INITIAL_REGISTERS_INDEX: &[(usize, usize)];
    const PATCH_INITIAL_REGISTER: Option<&str>;
    const FINAL_REGISTER_INDEX: Option<(usize, usize)>;

    fn test() {
        #[expect(non_snake_case)]
        let mut BROKEN_TESTS = vec![];
        for (_idline, line) in Self::TESTCASES
            .lines()
            .filter(|l| l.starts_with(Self::MATCH))
            .enumerate()
        {
            let chunk = &line[Self::MATCH.len() + 1..line.len() - 1].trim();
            // dbg!(idline, chunk);
            let mut fields = regex::Regex::new(r", |,")
                .unwrap()
                .split(chunk)
                .collect::<Vec<&str>>();
            if let Some(opinsert) = Self::PATCH_MATCH {
                fields.insert(0, opinsert);
            }
            let (field_imm, field_imm_u32) = if let Some(xid) = Self::PATCH_IMMEDIATE {
                if let Ok(val) = fields[xid].parse::<u32>() {
                    (val.to_string(), val)
                } else if let Ok(val) = fields[xid].parse::<i32>() {
                    (val.to_string(), val as u32)
                } else if let Ok(val) = u32::from_str_radix(&fields[xid][2..], 16) {
                    (val.to_string(), val)
                } else if let Ok(val) =
                    i32::from_str_radix(&("-".to_string() + &fields[xid][3..]), 16)
                {
                    (val.to_string(), val as u32)
                } else {
                    panic!("error parsing value {}", &fields[xid]);
                }
            } else {
                (String::new(), 0)
            };
            if let Some(xid) = Self::PATCH_IMMEDIATE {
                // dbg!(&field_imm);
                fields[xid] = &field_imm;
            }
            let instruction = {
                let mut instruction_fields = vec![String::new(); Self::OPFIELDS.len()];
                for i in 0..Self::OPFIELDS.len() {
                    instruction_fields[i] = fields[Self::OPFIELDS[i]].to_string();
                }
                if Self::PATCH_IMMEDIATE_WITH_REGISTER {
                    let (imm, reg) = (
                        instruction_fields.pop().unwrap(),
                        instruction_fields.pop().unwrap(),
                    );
                    instruction_fields.push(format!("{imm}({reg})"));
                }
                &instruction_fields.join(", ")
            };
            dbg!(instruction);
            let final_register = if let Some((xid, xval)) = Self::FINAL_REGISTER_INDEX {
                let i = fields[xid][1..].parse::<usize>().expect("expected reg id");
                if let Ok(val) = fields[xval].parse::<u32>() {
                    Some((i, val))
                } else if let Ok(val) = fields[xval].parse::<i32>() {
                    Some((i, val as u32))
                } else if let Ok(val) = u32::from_str_radix(&fields[xval][2..], 16) {
                    Some((i, val))
                } else if let Ok(val) =
                    i32::from_str_radix(&("-".to_string() + &fields[xval][3..]), 16)
                {
                    Some((i, val as u32))
                } else {
                    panic!("error parsing value {}", &fields[xval]);
                }
            } else {
                None
            };
            dbg!(final_register);
            let (initial_registers, init_reg_u32) = {
                let mut initial_registers = [0; 32];
                let mut init_regs_u32 = vec![];
                if let Some(val) = Self::PATCH_INITIAL_REGISTER {
                    fields.push(val);
                }
                for &(xid, xval) in Self::INITIAL_REGISTERS_INDEX {
                    let i = fields[xid][1..].parse::<usize>().expect("expected reg id");
                    if let Ok(val) = fields[xval].parse::<u32>() {
                        init_regs_u32.push(val);
                        initial_registers[i] = val;
                    } else if let Ok(val) = fields[xval].parse::<i32>() {
                        init_regs_u32.push(val as u32);
                        initial_registers[i] = val as u32;
                    } else if let Ok(val) = u32::from_str_radix(&fields[xval][2..], 16) {
                        init_regs_u32.push(val);
                        initial_registers[i] = val;
                    } else if let Ok(val) =
                        i32::from_str_radix(&("-".to_string() + &fields[xval][3..]), 16)
                    {
                        init_regs_u32.push(val as u32);
                        initial_registers[i] = val as u32;
                    } else {
                        panic!("error parsing value {}", &fields[xval]);
                    }
                    dbg!((i, initial_registers[i]));
                }
                (initial_registers, init_regs_u32)
            };

            // patch broken tests...
            if (Self::MATCH == "TEST_BRANCH_OP" && field_imm_u32 & 0b11 != 0 && {
                let [x, y]: [u32; 2] = init_reg_u32.try_into().unwrap();
                match fields[0] {
                    "beq" => x == y,
                    "bge" => (x as i32) >= (y as i32),
                    "bgeu" => x >= y,
                    "blt" => (x as i32) < (y as i32),
                    "bltu" => x < y,
                    "bne" => x != y,
                    _ => todo!(),
                }
            }) || (Self::MATCH == "TEST_JAL_OP" && field_imm_u32 & 0b11 != 0)
                || (Self::MATCH == "TEST_JALR_OP" && field_imm_u32 & 0b10 != 0)
                || (Self::MATCH == "TEST_LOAD"
                    && match fields[7] {
                        "lh" | "lhu" if field_imm_u32 & 0b01 != 0 => true,
                        "lw" if field_imm_u32 & 0b11 != 0 => true,
                        _ => false,
                    })
                || (Self::MATCH == "TEST_STORE"
                    && match fields[8] {
                        "sh" if field_imm_u32 & 0b01 != 0 => true,
                        "sw" if field_imm_u32 & 0b11 != 0 => true,
                        _ => false,
                    })
            {
                dbg!("broken test..");
                BROKEN_TESTS.push(format!("{chunk:40} -> {instruction:30}"));
                let should_panic = std::panic::catch_unwind(|| {
                    test_single_opcode(instruction, None, initial_registers, final_register)
                });
                assert!(should_panic
                    .unwrap_err()
                    .downcast_ref::<String>()
                    .unwrap()
                    .starts_with("unsatisfied"));
            } else {
                test_single_opcode(instruction, None, initial_registers, final_register);
            }
        }
        dbg!(&BROKEN_TESTS, BROKEN_TESTS.len());
    }
}

#[test]
#[ignore = "for debug only"]
fn debug_single_test() {
    let instruction = "and, x3, x1, x2";

    // let _bytecode = lib_rv32_asm::assemble_program(instruction).unwrap();

    let registers: [u32; 32] = [
        0, 4294920957, 4294920957, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
    ];

    let expected_rd_parts = Some((3, 0));

    test_single_opcode(instruction, None, registers, expected_rd_parts);
}
