// every keccak_k2 row the replayer emits for the keccak guest satisfies its circuit
use crate::tracers::oracles::transpiler_oracles::delegation::*;
use cs::cs::circuit_impl::BasicAssembly;
use cs::gkr_circuits::delegation::{keccak_chi5, keccak_column_parity, keccak_theta_rho};
use cs::tables::{IndexLookupFn, LookupWrapper, TableType};
use cs::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use field::baby_bear::base::BabyBearField;
use field::Mersenne31Field;
use riscv_transpiler::common_constants::delegation_types::keccak_k2::*;
use riscv_transpiler::common_constants::INITIAL_TIMESTAMP;
use riscv_transpiler::ir::simple_instruction_set::*;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::*;
use riscv_transpiler::vm::*;
use riscv_transpiler::witness::delegation::keccak_k2::*;
use riscv_transpiler::witness::*;

type F = BabyBearField;
type Debug = BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>;

#[derive(Default)]
struct Collector {
    column_parity: Vec<KeccakColumnParityDelegationWitness>,
    theta_rho: Vec<KeccakThetaRhoDelegationWitness>,
    chi5: Vec<KeccakChi5DelegationWitness>,
    add_sub_csrs: Vec<u16>,
}

impl WitnessTracer for Collector {
    fn needs_tracing_data_for_circuit_family<const FAMILY: u8>(&self) -> bool {
        FAMILY == riscv_transpiler::common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX
    }
    fn needs_tracing_data_for_delegation_type<const DELEGATION_TYPE: u16>(&self) -> bool {
        true
    }
    fn write_non_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        if data.opcode_data.delegation_type != 0 {
            self.add_sub_csrs.push(data.opcode_data.delegation_type);
        }
    }
    fn write_memory_family_data<const FAMILY: u8>(
        &mut self,
        _data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
    }
    fn write_delegation<
        const DELEGATION_TYPE: u16,
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
    >(
        &mut self,
        data: DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>,
    ) {
        unsafe {
            match DELEGATION_TYPE as u32 {
                KECCAK_COLUMN_PARITY_CSR_REGISTER => {
                    self.column_parity.push(core::mem::transmute_copy(&data))
                }
                KECCAK_THETA_RHO_CSR_REGISTER => {
                    self.theta_rho.push(core::mem::transmute_copy(&data))
                }
                KECCAK_CHI5_CSR_REGISTER => self.chi5.push(core::mem::transmute_copy(&data)),
                other => panic!("unexpected delegation {other}"),
            }
        }
    }
}

fn words(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap();
    bytes
        .chunks(4)
        .map(|c| {
            let mut w = [0u8; 4];
            w[..c.len()].copy_from_slice(c);
            u32::from_le_bytes(w)
        })
        .collect()
}

fn replay_example() -> Collector {
    let binary = words("../examples/keccak/app.bin");
    let text = words("../examples/keccak/app.text");
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 30;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter: SimpleSnapshotter<
        DelegationsAndFamiliesCounters,
        { riscv_transpiler::common_constants::rom::ROM_SECOND_WORD_BITS },
    > = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, state);
    VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, Mersenne31Field>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut (),
    );
    let cycles =
        (state.timestamp - INITIAL_TIMESTAMP) / riscv_transpiler::common_constants::TIMESTAMP_STEP;

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut ram_log = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ riscv_transpiler::common_constants::rom::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log,
    };
    let mut collector = Collector::default();
    ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, Mersenne31Field>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles as usize,
        &mut collector,
    );
    collector
}

fn leak<T>(v: Vec<T>) -> &'static [T] {
    Box::leak(v.into_boxed_slice())
}

fn full_membership<const W: usize>(t: TableType) -> LookupWrapper<F> {
    let mut table = t.generate_table::<F, W>();
    if let LookupWrapper::Initialized(inner) = &mut table {
        inner.quick_index_lookup_fn = IndexLookupFn::None;
    }
    table
}

fn check_rows<O: cs::oracle::Oracle<F> + 'static + Clone>(
    name: &str,
    oracles: Vec<O>,
    tables: &[(TableType, LookupWrapper<F>)],
    define: fn(&mut Debug),
) {
    for (i, oracle) in oracles.into_iter().enumerate() {
        let mut cs = Debug::new_with_oracle(oracle);
        for (t, table) in tables {
            cs::cs::circuit_trait::Circuit::add_table_with_content(&mut cs, *t, table.clone());
        }
        define(&mut cs);
        assert!(
            cs::cs::circuit_trait::Circuit::is_satisfied(&mut cs),
            "{name} row {i}"
        );
    }
}

#[test]
fn replayed_keccak_k2_rows_satisfy_their_circuits() {
    let collected = replay_example();
    let perms = collected.column_parity.len() / NUM_KECCAK_K2_COLUMN_PARITY_CALLS;
    assert!(perms >= 3, "{perms}");
    assert_eq!(
        collected.column_parity.len(),
        perms * NUM_KECCAK_K2_COLUMN_PARITY_CALLS
    );
    assert_eq!(
        collected.theta_rho.len(),
        perms * NUM_KECCAK_K2_THETA_RHO_CALLS
    );
    assert_eq!(collected.chi5.len(), perms * NUM_KECCAK_K2_CHI5_CALLS);
    let expected_csrs: Vec<u16> = (0..perms)
        .flat_map(|_| {
            (0..NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600).map(|j| keccak_k2_call_csr(j) as u16)
        })
        .collect();
    assert_eq!(collected.add_sub_csrs, expected_csrs);

    let cp: &'static [KeccakColumnParityDelegationWitness] = leak(collected.column_parity);
    let tr: &'static [KeccakThetaRhoDelegationWitness] = leak(collected.theta_rho);
    let chi: &'static [KeccakChi5DelegationWitness] = leak(collected.chi5);

    let cp_tables: Vec<_> = keccak_column_parity::all_table_types()
        .into_iter()
        .map(|t| (t, full_membership::<7>(t)))
        .collect();
    check_rows(
        "column parity",
        (0..cp.len())
            .map(|i| KeccakColumnParityDelegationOracle {
                cycle_data: &cp[i..i + 1],
                marker: core::marker::PhantomData,
            })
            .collect(),
        &cp_tables,
        keccak_column_parity::define_keccak_column_parity_delegation_circuit,
    );
    let tr_tables: Vec<_> = keccak_theta_rho::all_table_types()
        .into_iter()
        .map(|t| (t, full_membership::<8>(t)))
        .collect();
    check_rows(
        "theta/rho",
        (0..tr.len())
            .map(|i| KeccakThetaRhoDelegationOracle {
                cycle_data: &tr[i..i + 1],
                marker: core::marker::PhantomData,
            })
            .collect(),
        &tr_tables,
        keccak_theta_rho::define_keccak_theta_rho_delegation_circuit,
    );
    let mut chi_driver = cs::tables::TableDriver::<F>::new();
    keccak_chi5::keccak_chi5_table_driver_fn(&mut chi_driver);
    let chi_tables: Vec<_> = keccak_chi5::CHI5_TABLE_TYPES
        .into_iter()
        .map(|t| {
            let mut table = chi_driver.tables[t as usize].clone();
            if let LookupWrapper::Initialized(inner) = &mut table {
                inner.quick_index_lookup_fn = IndexLookupFn::None;
            }
            (t, table)
        })
        .collect();
    check_rows(
        "chi5",
        (0..chi.len())
            .map(|i| KeccakChi5DelegationOracle {
                cycle_data: &chi[i..i + 1],
                marker: core::marker::PhantomData,
            })
            .collect(),
        &chi_tables,
        keccak_chi5::define_keccak_chi5_delegation_circuit,
    );
}
