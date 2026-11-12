//! The input recipe shared by committed CPU proofs and GPU circuit parity.
//!
//! Capture returns raw replay rows, optional decoder entries and sparse final RAM.
//! It never evaluates a padded witness, commits an oracle or proves a circuit.
//! Paths are relative to an explicit workspace root; environment filters and
//! experiment configuration overrides do not select canonical inputs.

use super::common::{run_vm_and_capture, ProgramConfig, VmRunOutput};
use crate::definitions::{FinalRegisterValue, SoundnessMode};
use crate::gkr::prover_config::{ProofProfile, ProverConfig};
use crate::gkr::witness_gen::family_circuits::build_unified_table_driver;
use common_constants::circuit_families::*;
use common_constants::keccak_f1600::*;
use common_constants::{bigint_with_control::*, blake2s_with_control::*, keccak_special5::*};
use common_constants::{TimestampScalar, NON_DETERMINISM_CSR, ROM_SECOND_WORD_BITS, ROM_WORD_SIZE};
use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
use cs::gkr_circuits::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::tables::TableDriver;
use field::baby_bear::base::BabyBearField as BF;
use riscv_transpiler::ir::simple_instruction_set::InstructionName;
use riscv_transpiler::ir::{FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig};
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, DelegationsAndUnifiedCounters, ReplayBuffer,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_f1600::{
    KeccakChi5DelegationWitness, KeccakColumnParityDelegationWitness,
    KeccakThetaRhoDelegationWitness,
};
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    DelegationDestinationHolder, DelegationWitness, MemDestinationHolder,
    MemoryOpcodeTracingDataWithTimestamp, NonMemDestinationHolder,
    NonMemoryOpcodeTracingDataWithTimestamp, UnifiedDestinationHolder,
    UnifiedOpcodeTracingDataWithTimestamp, WitnessTracer,
};
use std::alloc::Global;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use worker::Worker;

/// Exactly one Standard proof per entry and soundness mode. G-function is not
/// part of this set; legacy special5 remains required by the committed OS guest.
pub const CANONICAL_CIRCUITS: [CanonicalCircuit; 14] = [
    CanonicalCircuit::AddSubLuiAuipcMop,
    CanonicalCircuit::JumpBranchSlt,
    CanonicalCircuit::ShiftBinop,
    CanonicalCircuit::UnsignedMulDiv,
    CanonicalCircuit::MemWordOnly,
    CanonicalCircuit::MemSubwordOnly,
    CanonicalCircuit::InitsAndTeardowns,
    CanonicalCircuit::UnifiedReducedMachine,
    CanonicalCircuit::BigintWithExtendedControl,
    CanonicalCircuit::Blake2WithExtendedControl,
    CanonicalCircuit::KeccakSpecial5,
    CanonicalCircuit::KeccakColumnParity,
    CanonicalCircuit::KeccakThetaRho,
    CanonicalCircuit::KeccakChi5,
];

pub const PESSIMISTIC_CANONICAL_CIRCUITS: [CanonicalCircuit; 2] = [
    CanonicalCircuit::Compression,
    CanonicalCircuit::CompressionFinal,
];

pub fn canonical_circuits(mode: SoundnessMode) -> impl Iterator<Item = CanonicalCircuit> {
    CANONICAL_CIRCUITS.into_iter().chain(
        PESSIMISTIC_CANONICAL_CIRCUITS
            .into_iter()
            .filter(move |_| mode == SoundnessMode::PessimisticConjecture),
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CanonicalCircuit {
    AddSubLuiAuipcMop,
    JumpBranchSlt,
    ShiftBinop,
    UnsignedMulDiv,
    MemWordOnly,
    MemSubwordOnly,
    InitsAndTeardowns,
    UnifiedReducedMachine,
    Compression,
    CompressionFinal,
    BigintWithExtendedControl,
    Blake2WithExtendedControl,
    KeccakSpecial5,
    KeccakColumnParity,
    KeccakThetaRho,
    KeccakChi5,
}

impl CanonicalCircuit {
    pub const fn stem(self) -> &'static str {
        match self {
            Self::AddSubLuiAuipcMop => "add_sub_lui_auipc_mop",
            Self::JumpBranchSlt => "jump_branch_slt",
            Self::ShiftBinop => "shift_binop",
            Self::UnsignedMulDiv => "unsigned_mul_div",
            Self::MemWordOnly => "mem_word_only",
            Self::MemSubwordOnly => "mem_subword_only",
            Self::InitsAndTeardowns => "inits_and_teardowns",
            Self::UnifiedReducedMachine => "unified_reduced_machine",
            Self::Compression => "compression",
            Self::CompressionFinal => "compression_final",
            Self::BigintWithExtendedControl => "bigint_with_extended_control",
            Self::Blake2WithExtendedControl => "blake2_with_extended_control",
            Self::KeccakSpecial5 => "keccak_special5",
            Self::KeccakColumnParity => "keccak_column_parity",
            Self::KeccakThetaRho => "keccak_theta_rho",
            Self::KeccakChi5 => "keccak_chi5",
        }
    }

    pub const fn definition_directory(self) -> &'static str {
        match self {
            Self::AddSubLuiAuipcMop => "unrolled_circuits/add_sub_lui_auipc_mop",
            Self::JumpBranchSlt => "unrolled_circuits/jump_branch_slt",
            Self::ShiftBinop => "unrolled_circuits/shift_binary",
            Self::UnsignedMulDiv => "unrolled_circuits/mul_div_unsigned",
            Self::MemWordOnly => "unrolled_circuits/load_store_word_only",
            Self::MemSubwordOnly => "unrolled_circuits/load_store_subword_only",
            Self::InitsAndTeardowns => "unrolled_circuits/inits_and_teardowns",
            Self::UnifiedReducedMachine | Self::Compression => {
                "unrolled_circuits/unified_reduced_machine"
            }
            Self::CompressionFinal => "unrolled_circuits/unified_reduced_machine_2_22",
            Self::BigintWithExtendedControl => "bigint_with_control",
            Self::Blake2WithExtendedControl => "blake2_with_compression",
            Self::KeccakSpecial5 => "keccak_special5",
            Self::KeccakColumnParity => "keccak_column_parity",
            Self::KeccakThetaRho => "keccak_theta_rho",
            Self::KeccakChi5 => "keccak_chi5",
        }
    }

    pub const fn workload(self) -> CanonicalWorkload {
        match self {
            Self::AddSubLuiAuipcMop | Self::ShiftBinop => CanonicalWorkload::MopSmoke,
            Self::UnsignedMulDiv => CanonicalWorkload::HashedFibonacciCompression,
            Self::BigintWithExtendedControl => CanonicalWorkload::Bigint,
            Self::UnifiedReducedMachine
            | Self::Compression
            | Self::CompressionFinal
            | Self::Blake2WithExtendedControl => CanonicalWorkload::CompressionSmoke,
            Self::KeccakColumnParity | Self::KeccakThetaRho | Self::KeccakChi5 => {
                CanonicalWorkload::Keccak
            }
            Self::JumpBranchSlt
            | Self::MemWordOnly
            | Self::MemSubwordOnly
            | Self::InitsAndTeardowns
            | Self::KeccakSpecial5 => CanonicalWorkload::LegacyKeccak,
        }
    }

    pub const fn family_index(self) -> Option<u8> {
        match self {
            Self::AddSubLuiAuipcMop => Some(ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX),
            Self::JumpBranchSlt => Some(JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX),
            Self::ShiftBinop => Some(SHIFT_BINARY_CIRCUIT_FAMILY_IDX),
            Self::UnsignedMulDiv => Some(MUL_DIV_CIRCUIT_FAMILY_IDX),
            Self::MemWordOnly => Some(LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX),
            Self::MemSubwordOnly => Some(LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX),
            Self::UnifiedReducedMachine | Self::Compression | Self::CompressionFinal => {
                Some(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
            }
            _ => None,
        }
    }

    fn generated_path(self, root: &Path, name: &str) -> PathBuf {
        root.join("circuit_defs")
            .join(self.definition_directory())
            .join("generated")
            .join(name)
    }

    pub fn compiled_circuit(self, root: &Path) -> GKRCircuitArtifact<BF> {
        read_json(&self.generated_path(root, "layout.json"))
    }

    pub fn prover_config(self, root: &Path, mode: SoundnessMode) -> ProverConfig {
        let profile = match self {
            Self::Compression => Some((ProofProfile::Compression, 23)),
            Self::CompressionFinal => Some((ProofProfile::CompressionFinal, 22)),
            _ => None,
        };
        if let Some((profile, trace_len_log2)) = profile {
            return profile.prover_config(trace_len_log2, mode);
        }
        read_json(&self.generated_path(
            root,
            &format!("prover_config_sec_100_{}.json", mode.file_suffix()),
        ))
    }

    pub fn proof_path(self, root: &Path, mode: SoundnessMode) -> PathBuf {
        proof_fixtures::circuit_proof_in(root, mode.file_suffix(), self.stem())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CanonicalWorkload {
    MopSmoke,
    HashedFibonacciCompression,
    Bigint,
    CompressionSmoke,
    LegacyKeccak,
    Keccak,
}

impl CanonicalWorkload {
    pub const fn program_stem(self) -> &'static str {
        match self {
            Self::MopSmoke => "examples/mop_smoke/app",
            Self::HashedFibonacciCompression => {
                "examples/hashed_fibonacci/app_blake2_with_compression"
            }
            Self::Bigint => "examples/bigint_with_control/app",
            Self::CompressionSmoke => "examples/multi_family_smoke/app_blake2_with_compression",
            Self::LegacyKeccak => "riscv_transpiler/examples/keccak_f1600/app",
            Self::Keccak => "examples/keccak/app",
        }
    }

    pub const fn non_determinism_reads(self) -> &'static [u32] {
        match self {
            Self::MopSmoke | Self::HashedFibonacciCompression | Self::LegacyKeccak => &[15, 1],
            Self::CompressionSmoke => &[50, 0xDEAD_BEEF],
            Self::Bigint | Self::Keccak => &[],
        }
    }

    pub const fn ram_bound_bytes(self) -> usize {
        match self {
            Self::LegacyKeccak | Self::Keccak => 1 << 29,
            _ => 1 << 30,
        }
    }

    pub fn program_config(self, root: &Path) -> ProgramConfig {
        ProgramConfig {
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                root.join(format!("{}.bin", self.program_stem())),
                root.join(format!("{}.text", self.program_stem())),
            ),
            non_determinism_reads: self.non_determinism_reads().to_vec(),
            cycles_bound: 1 << 20,
            ram_bound_bytes: self.ram_bound_bytes(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CanonicalTrace {
    NonMemory(Vec<NonMemoryOpcodeTracingDataWithTimestamp>),
    Memory(Vec<MemoryOpcodeTracingDataWithTimestamp>),
    Unified(Vec<UnifiedOpcodeTracingDataWithTimestamp>),
    Bigint(Vec<BigintDelegationWitness>),
    Blake2WithCompression(Vec<Blake2sRoundFunctionDelegationWitness>),
    KeccakSpecial5(Vec<KeccakSpecial5DelegationWitness>),
    KeccakColumnParity(Vec<KeccakColumnParityDelegationWitness>),
    KeccakThetaRho(Vec<KeccakThetaRhoDelegationWitness>),
    KeccakChi5(Vec<KeccakChi5DelegationWitness>),
    InitsAndTeardowns,
}

impl CanonicalTrace {
    pub fn len(&self) -> usize {
        match self {
            Self::NonMemory(rows) => rows.len(),
            Self::Memory(rows) => rows.len(),
            Self::Unified(rows) => rows.len(),
            Self::Bigint(rows) => rows.len(),
            Self::Blake2WithCompression(rows) => rows.len(),
            Self::KeccakSpecial5(rows) => rows.len(),
            Self::KeccakColumnParity(rows) => rows.len(),
            Self::KeccakThetaRho(rows) => rows.len(),
            Self::KeccakChi5(rows) => rows.len(),
            Self::InitsAndTeardowns => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalBoundary {
    pub registers: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
}

/// Global byte addresses in increasing order; ROM values have already been
/// masked to zero by the simulator's shuffle-RAM collector. No dense columns.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SparseInitsAndTeardowns {
    pub touched: Vec<(u32, (TimestampScalar, u32))>,
    pub top_bits: Vec<u32>,
}

pub struct CanonicalInputs {
    pub circuit: CanonicalCircuit,
    pub compiled_circuit: GKRCircuitArtifact<BF>,
    pub binary: Vec<u32>,
    pub text_section: Vec<u32>,
    pub table_driver: TableDriver<BF>,
    /// Preserve `None` for CPU setup; GPU witness adapters may flatten it later.
    pub decoder_table: Vec<Option<ExecutorFamilyDecoderData>>,
    pub trace: CanonicalTrace,
    pub inits_and_teardowns: Option<SparseInitsAndTeardowns>,
    pub boundary: CanonicalBoundary,
}

#[derive(Clone, Copy)]
struct DelegationCounts {
    bigint: usize,
    blake: usize,
    special5: usize,
    keccak: usize,
    g_function: usize,
}

/// Callers use eight workers for canonical production; accepting a worker also
/// lets the CPU replay test verify independence from parallel RAM partitioning.
pub fn capture_canonical_inputs(
    root: &Path,
    circuit: CanonicalCircuit,
    worker: &Worker,
) -> CanonicalInputs {
    let config = circuit.workload().program_config(root);
    macro_rules! capture {
        ($counters:ty, $decoder:ty) => {{
            let vm = run_vm_and_capture::<$counters, $decoder>(&config, worker);
            let counts = DelegationCounts {
                bigint: vm.counters.bigint_calls,
                blake: vm.counters.blake_calls,
                special5: vm.counters.keccak_calls,
                keccak: vm.counters.keccak_f1600_calls,
                g_function: vm.counters.blake_g_function_calls,
            };
            finish_capture(root, circuit, vm, counts)
        }};
    }
    if circuit.workload() == CanonicalWorkload::CompressionSmoke {
        capture!(DelegationsAndUnifiedCounters, ReducedMachineDecoderConfig)
    } else {
        capture!(
            DelegationsAndFamiliesCounters,
            FullUnsignedMachineDecoderConfig
        )
    }
}

fn finish_capture<C: Counters + Default>(
    root: &Path,
    circuit: CanonicalCircuit,
    vm: VmRunOutput<C>,
    counts: DelegationCounts,
) -> CanonicalInputs {
    let compiled_circuit = circuit.compiled_circuit(root);
    let trace_len = compiled_circuit.trace_len;
    let boundary = CanonicalBoundary {
        registers: vm.final_state.registers.map(|register| FinalRegisterValue {
            value: register.value,
            last_access_timestamp: register.timestamp,
        }),
        final_pc: vm.final_pc(),
        final_timestamp: vm.final_timestamp(),
    };
    if circuit.workload() == CanonicalWorkload::MopSmoke {
        for name in [
            InstructionName::ZimopAdd,
            InstructionName::ZimopSub,
            InstructionName::ZimopMul,
            InstructionName::ZimopFMA,
            InstructionName::Rev8,
        ] {
            assert!(vm
                .instructions
                .iter()
                .any(|instruction| instruction.name == name));
        }
        assert_eq!(boundary.registers[17].value, 0xC0FF_EE00);
    }
    if circuit.workload() == CanonicalWorkload::CompressionSmoke {
        assert!(counts.blake > 0);
        assert_eq!(
            counts.bigint + counts.special5 + counts.keccak + counts.g_function,
            0
        );
    }
    if circuit.workload() == CanonicalWorkload::Keccak {
        assert_eq!(keccak_f1600_permutations(counts.keccak), 3);
        assert_eq!(counts.special5, 0);
    }

    let decoder_table = decoder_table(circuit, &vm.text_section);
    let table_driver = table_driver(circuit, &vm.binary);
    assert_eq!(
        table_driver.total_tables_len + decoder_table.len(),
        compiled_circuit.total_tables_size
    );

    macro_rules! delegation {
        ($variant:ident, $csr:expr, $r:expr, $ir:expr, $iw:expr, $vo:expr, $count:expr) => {
            CanonicalTrace::$variant(replay_delegation::<C, $csr, $r, $ir, $iw, $vo>(&vm, $count))
        };
    }
    let trace = match circuit {
        CanonicalCircuit::AddSubLuiAuipcMop => CanonicalTrace::NonMemory(replay_non_memory::<
            ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
            C,
        >(&vm)),
        CanonicalCircuit::JumpBranchSlt => CanonicalTrace::NonMemory(replay_non_memory::<
            JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
            C,
        >(&vm)),
        CanonicalCircuit::ShiftBinop => {
            CanonicalTrace::NonMemory(replay_non_memory::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX, C>(&vm))
        }
        CanonicalCircuit::UnsignedMulDiv => {
            CanonicalTrace::NonMemory(replay_non_memory::<MUL_DIV_CIRCUIT_FAMILY_IDX, C>(&vm))
        }
        CanonicalCircuit::MemWordOnly => CanonicalTrace::Memory(replay_memory::<
            LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
            C,
        >(&vm)),
        CanonicalCircuit::MemSubwordOnly => CanonicalTrace::Memory(replay_memory::<
            LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
            C,
        >(&vm)),
        CanonicalCircuit::UnifiedReducedMachine
        | CanonicalCircuit::Compression
        | CanonicalCircuit::CompressionFinal => {
            let mut rows = vec![
                UnifiedOpcodeTracingDataWithTimestamp::default();
                vm.counters
                    .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>(
                    )
            ];
            let mut buffers = [rows.as_mut_slice()];
            let mut tracer = UnifiedDestinationHolder {
                buffers: &mut buffers,
            };
            replay(&vm, &mut tracer);
            assert!(tracer.buffers.is_empty());
            CanonicalTrace::Unified(rows)
        }
        CanonicalCircuit::BigintWithExtendedControl => delegation!(
            Bigint,
            { BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16 },
            NUM_BIGINT_REGISTER_ACCESSES,
            BIGINT_X11_NUM_READS,
            BIGINT_X10_NUM_WRITES,
            NUM_BIGINT_VARIABLE_OFFSETS,
            counts.bigint
        ),
        CanonicalCircuit::Blake2WithExtendedControl => delegation!(
            Blake2WithCompression,
            { BLAKE2S_DELEGATION_CSR_REGISTER as u16 },
            NUM_BLAKE2S_REGISTER_ACCESSES,
            BLAKE2S_X11_NUM_READS,
            BLAKE2S_X10_NUM_WRITES,
            NUM_BLAKE2S_VARIABLE_OFFSETS,
            counts.blake
        ),
        CanonicalCircuit::KeccakSpecial5 => delegation!(
            KeccakSpecial5,
            { KECCAK_SPECIAL5_CSR_REGISTER as u16 },
            NUM_KECCAK_SPECIAL5_REGISTER_ACCESSES,
            NUM_KECCAK_SPECIAL5_INDIRECT_READS,
            KECCAK_SPECIAL5_X11_NUM_WRITES,
            KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS,
            counts.special5
        ),
        CanonicalCircuit::KeccakColumnParity => delegation!(
            KeccakColumnParity,
            { KECCAK_COLUMN_PARITY_CSR_REGISTER as u16 },
            NUM_KECCAK_F1600_REGISTER_ACCESSES,
            NUM_KECCAK_F1600_INDIRECT_READS,
            KECCAK_COLUMN_PARITY_X11_NUM_WRITES,
            KECCAK_COLUMN_PARITY_NUM_VARIABLE_OFFSETS,
            keccak_f1600_permutations(counts.keccak) * NUM_KECCAK_F1600_COLUMN_PARITY_CALLS
        ),
        CanonicalCircuit::KeccakThetaRho => delegation!(
            KeccakThetaRho,
            { KECCAK_THETA_RHO_CSR_REGISTER as u16 },
            NUM_KECCAK_F1600_REGISTER_ACCESSES,
            NUM_KECCAK_F1600_INDIRECT_READS,
            KECCAK_THETA_RHO_X11_NUM_WRITES,
            KECCAK_THETA_RHO_NUM_VARIABLE_OFFSETS,
            keccak_f1600_permutations(counts.keccak) * NUM_KECCAK_F1600_THETA_RHO_CALLS
        ),
        CanonicalCircuit::KeccakChi5 => delegation!(
            KeccakChi5,
            { KECCAK_CHI5_CSR_REGISTER as u16 },
            NUM_KECCAK_F1600_REGISTER_ACCESSES,
            NUM_KECCAK_F1600_INDIRECT_READS,
            KECCAK_CHI5_X11_NUM_WRITES,
            KECCAK_CHI5_NUM_VARIABLE_OFFSETS,
            keccak_f1600_permutations(counts.keccak) * NUM_KECCAK_F1600_CHI5_CALLS
        ),
        CanonicalCircuit::InitsAndTeardowns => CanonicalTrace::InitsAndTeardowns,
    };
    if circuit != CanonicalCircuit::InitsAndTeardowns {
        assert!(!trace.is_empty(), "{} has no real rows", circuit.stem());
        assert!(
            trace.len() < trace_len,
            "{} needs multiple instances",
            circuit.stem()
        );
    }

    let inits_and_teardowns = if matches!(
        circuit,
        CanonicalCircuit::InitsAndTeardowns
            | CanonicalCircuit::UnifiedReducedMachine
            | CanonicalCircuit::Compression
            | CanonicalCircuit::CompressionFinal
    ) {
        let touched: Vec<_> = vm
            .shuffle_ram_touched_addresses
            .iter()
            .flatten()
            .copied()
            .collect();
        assert!(!touched.is_empty());
        assert!(touched.windows(2).all(|pair| pair[0].0 < pair[1].0));
        let sets = compiled_circuit.memory_layout.teardown_sets.len();
        let log_rows = trace_len.trailing_zeros();
        let mut selected: BTreeSet<u32> = touched
            .iter()
            .map(|&(address, _)| (address >> 2) >> log_rows)
            .collect();
        assert!(
            selected.len() <= sets,
            "canonical run needs multiple i/t groups"
        );
        if circuit == CanonicalCircuit::InitsAndTeardowns {
            assert_eq!(sets * trace_len * 4, circuit.workload().ram_bound_bytes());
            selected = (0..sets as u32).collect();
        } else {
            // Production fills the lowest available holes, then emits sorted
            // top bits. Reproduce selection without allocating dense columns.
            let mut padding = 0;
            while selected.len() < sets {
                selected.insert(padding);
                padding += 1;
            }
        }
        Some(SparseInitsAndTeardowns {
            touched,
            top_bits: selected.into_iter().collect(),
        })
    } else {
        None
    };
    CanonicalInputs {
        circuit,
        compiled_circuit,
        binary: vm.binary,
        text_section: vm.text_section,
        table_driver,
        decoder_table,
        trace,
        inits_and_teardowns,
        boundary,
    }
}

fn replay<C: Counters + Default, T: WitnessTracer>(vm: &VmRunOutput<C>, tracer: &mut T) {
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut logs = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> { ram_log: &mut logs };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BF>(
        &mut state,
        &mut ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        tracer,
    );
    assert_eq!(state, vm.expected_final_state());
}

fn replay_non_memory<const FAMILY: u8, C: Counters + Default>(
    vm: &VmRunOutput<C>,
) -> Vec<NonMemoryOpcodeTracingDataWithTimestamp> {
    let mut rows = vec![
        NonMemoryOpcodeTracingDataWithTimestamp::default();
        vm.counters.get_calls_to_circuit_family::<FAMILY>()
    ];
    let mut buffers = [rows.as_mut_slice()];
    let mut tracer = NonMemDestinationHolder::<FAMILY> {
        buffers: &mut buffers,
    };
    replay(vm, &mut tracer);
    assert!(tracer.buffers.is_empty());
    rows
}

fn replay_memory<const FAMILY: u8, C: Counters + Default>(
    vm: &VmRunOutput<C>,
) -> Vec<MemoryOpcodeTracingDataWithTimestamp> {
    let mut rows = vec![
        MemoryOpcodeTracingDataWithTimestamp::default();
        vm.counters.get_calls_to_circuit_family::<FAMILY>()
    ];
    let mut buffers = [rows.as_mut_slice()];
    let mut tracer = MemDestinationHolder::<FAMILY> {
        buffers: &mut buffers,
    };
    replay(vm, &mut tracer);
    assert!(tracer.buffers.is_empty());
    rows
}

fn replay_delegation<
    C: Counters + Default,
    const CSR: u16,
    const R: usize,
    const IR: usize,
    const IW: usize,
    const VO: usize,
>(
    vm: &VmRunOutput<C>,
    count: usize,
) -> Vec<DelegationWitness<R, IR, IW, VO>> {
    let mut rows = vec![DelegationWitness::empty(); count];
    let mut buffers = [rows.as_mut_slice()];
    let mut tracer = DelegationDestinationHolder::<CSR, R, IR, IW, VO> {
        buffers: &mut buffers,
    };
    replay(vm, &mut tracer);
    assert!(tracer.buffers.is_empty());
    rows
}

const SUPPORTED_CSRS: &[u16] = &[
    NON_DETERMINISM_CSR as u16,
    BLAKE2S_DELEGATION_CSR_REGISTER as u16,
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
    KECCAK_SPECIAL5_CSR_REGISTER as u16,
    KECCAK_COLUMN_PARITY_CSR_REGISTER as u16,
    KECCAK_THETA_RHO_CSR_REGISTER as u16,
    KECCAK_CHI5_CSR_REGISTER as u16,
];

fn decoder_table(
    circuit: CanonicalCircuit,
    text: &[u32],
) -> Vec<Option<ExecutorFamilyDecoderData>> {
    let Some(family) = circuit.family_index() else {
        return Vec::new();
    };
    if matches!(
        circuit,
        CanonicalCircuit::UnifiedReducedMachine
            | CanonicalCircuit::Compression
            | CanonicalCircuit::CompressionFinal
    ) {
        let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> =
            vec![Box::new(UnifiedReducedMachineDecoder)];
        process_binary_into_separate_tables_ext::<BF, ReducedMachineDecoderConfig, true, Global>(
            text,
            &decoders,
            ROM_WORD_SIZE,
            SUPPORTED_CSRS,
        )
        .remove(&family)
        .unwrap()
    } else {
        process_binary_into_separate_tables_ext::<BF, FullUnsignedMachineDecoderConfig, true, Global>(
            text, &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
            1 << 20, SUPPORTED_CSRS,
        ).remove(&family).unwrap()
    }
}

fn table_driver(circuit: CanonicalCircuit, binary: &[u32]) -> TableDriver<BF> {
    use cs::gkr_circuits::{
        add_sub_family, binary_shifts_family, delegation, jump_branch_slt_family, mem_subword_only,
        mem_word_only, mul_div,
    };
    let mut tables = TableDriver::new();
    match circuit {
        CanonicalCircuit::AddSubLuiAuipcMop => add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut tables),
        CanonicalCircuit::JumpBranchSlt => jump_branch_slt_family::jump_branch_slt_table_driver_fn(&mut tables),
        CanonicalCircuit::ShiftBinop => binary_shifts_family::shift_binop_table_driver_fn(&mut tables),
        CanonicalCircuit::UnsignedMulDiv => mul_div::mul_div_table_driver_fn::<BF, false>(&mut tables),
        CanonicalCircuit::MemWordOnly => {
            mem_word_only::mem_word_only_table_driver_fn(&mut tables);
            for (kind, table) in mem_word_only::create_mem_word_only_special_tables::<BF, { ROM_SECOND_WORD_BITS }>(binary) {
                tables.add_table_with_content(kind, table);
            }
        }
        CanonicalCircuit::MemSubwordOnly => {
            mem_subword_only::mem_subword_only_table_driver_fn(&mut tables);
            for (kind, table) in mem_subword_only::create_mem_subword_only_special_tables::<BF, { ROM_SECOND_WORD_BITS }>(binary) {
                tables.add_table_with_content(kind, table);
            }
        }
        CanonicalCircuit::UnifiedReducedMachine | CanonicalCircuit::Compression | CanonicalCircuit::CompressionFinal => return build_unified_table_driver(binary),
        CanonicalCircuit::BigintWithExtendedControl => delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(&mut tables),
        CanonicalCircuit::Blake2WithExtendedControl => delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(&mut tables),
        CanonicalCircuit::KeccakSpecial5 => delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(&mut tables),
        CanonicalCircuit::KeccakColumnParity => delegation::keccak_column_parity::keccak_column_parity_delegation_circuit_table_driver_fn(&mut tables),
        CanonicalCircuit::KeccakThetaRho => delegation::keccak_theta_rho::keccak_theta_rho_delegation_circuit_table_driver_fn(&mut tables),
        CanonicalCircuit::KeccakChi5 => delegation::keccak_chi5::keccak_chi5_delegation_circuit_table_driver_fn(&mut tables),
        CanonicalCircuit::InitsAndTeardowns => {}
    }
    tables
}

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> T {
    serde_json::from_reader(std::io::BufReader::new(std::fs::File::open(path).unwrap())).unwrap()
}
