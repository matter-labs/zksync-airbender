#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::TableDriver;
use definitions::MerkleTreeCap;
use merkle_trees::DefaultTreeConstructor;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::fft::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::*;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::*;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::tracers::*;
use prover::*;
use riscv_transpiler::cycle::*;
use std::alloc::Global;
use std::path::Path;
use worker::Worker;

pub use ::add_sub_lui_auipc_mop::AddSubLuiAuipcMopCircuit;
pub use ::jump_branch_slt::JumpBranchSltCircuit;
pub use ::load_store_subword_only::LoadStoreSubwordOnlyCircuit;
pub use ::load_store_word_only::LoadStoreWordOnlyCircuit;
pub use ::mul_div_unsigned::UnsignedMulDivCircuit;
pub use ::shift_binary::ShiftBinaryCircuit;

pub use ::bigint_with_control::BigIntDelegationCircuit;
pub use ::blake2_g_function::Blake2sGFunctionDelegationCircuit;
pub use ::blake2_with_compression::Blake2sWithCompressionDelegationCircuit;
pub use ::keccak_special5::KeccakSpecial5DelegationCircuit;

pub use ::inits_and_teardowns;

pub use bigint_with_control;
pub use blake2_g_function;
pub use blake2_with_compression;
pub use keccak_special5;
pub use prover;

pub mod circuits;
pub mod program_setups;
pub mod unrolled_circuits;
pub use self::circuits::*;
pub use self::unrolled_circuits::*;

pub fn pad_bytecode_bytes_for_proving(bytecode: &mut Vec<u8>) {
    assert!(bytecode.len() <= common_constants::ROM_BYTE_SIZE);
    bytecode.resize(common_constants::ROM_BYTE_SIZE, 0);
}

pub fn pad_bytecode_for_proving(bytecode: &mut Vec<u32>) {
    assert!(bytecode.len() <= common_constants::ROM_WORD_SIZE);
    bytecode.resize(common_constants::ROM_WORD_SIZE, 0);
}

pub fn is_default_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IMStandardIsaConfig>()
}

pub fn is_reduced_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<ReducedMachineWithDelegation>()
}

pub fn is_machine_without_signed_mul_div_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IMStandardIsaConfigUnsignedMulDivOnly>()
}

pub fn is_final_reduced_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<ReducedMachineWithoutDelegation>()
}

pub enum UnrolledCircuitWitnessEvalFn<A: GoodAllocator> {
    NonMemory {
        witness_fn:
            fn(&'_ mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
        decoder_table: Vec<Option<ExecutorFamilyDecoderData>, A>,
        default_pc_value_in_padding: u32,
    },
    Memory {
        witness_fn: fn(&'_ mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
        decoder_table: Vec<Option<ExecutorFamilyDecoderData>, A>,
    },
    Unified {
        witness_fn:
            fn(&'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>),
        decoder_table: Vec<Option<ExecutorFamilyDecoderData>, A>,
    },
}

pub struct CircuitSetup<A: GoodAllocator = Global> {
    pub family_idx: u8,
    pub trace_len: usize,
    pub compiled_circuit: GKRCircuitArtifact<BabyBearField>,
    pub table_driver: TableDriver<BabyBearField>,
    pub setup: GKRSetup<BabyBearField>,
    pub witness_eval_fn: Option<UnrolledCircuitWitnessEvalFn<A>>,
}

pub fn make_setup_for_non_mem_circuit<
    C: circuit_common::RiscVCycleCircuit<BabyBearField, false>,
    A: GoodAllocator,
>(
    witness_eval_fn: Option<
        fn(&'_ mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
    >,
    default_pc_value_in_padding: u32,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
) -> CircuitSetup<A> {
    let circuit = circuit_common::risc_v_non_mem_get_circuit::<BabyBearField, C>(use_caches);
    let table_driver = circuit_common::risc_v_non_mem_get_table_driver::<BabyBearField, C>();
    let setup = GKRSetup::construct(
        &table_driver,
        &decoder_table_data,
        1 << C::DOMAIN_SIZE_LOG2,
        &circuit,
    );

    let mut witness_gen_data = Vec::new_in(A::default());
    for el in decoder_table_data.iter() {
        let t = el.as_ref().copied().unwrap_or(Default::default());
        witness_gen_data.push(t);
    }

    let witness_eval_fn = witness_eval_fn.map(|el| UnrolledCircuitWitnessEvalFn::NonMemory {
        witness_fn: el,
        decoder_table: decoder_table_data.to_vec_in(A::default()),
        default_pc_value_in_padding,
    });

    CircuitSetup {
        family_idx: C::CIRCUIT_FAMILY,
        trace_len: 1 << C::DOMAIN_SIZE_LOG2,
        compiled_circuit: circuit,
        table_driver,
        setup,
        witness_eval_fn,
    }
}

pub fn make_setup_for_with_mem_circuit<
    C: circuit_common::RiscVCycleCircuit<BabyBearField, true>,
    A: GoodAllocator,
>(
    witness_eval_fn: Option<
        fn(&'_ mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
    >,
    bytecode: &[u32],
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
) -> CircuitSetup<A> {
    let circuit =
        circuit_common::risc_v_with_mem_get_circuit::<BabyBearField, C>(use_caches, bytecode);
    let table_driver =
        circuit_common::risc_v_with_mem_get_table_driver::<BabyBearField, C>(bytecode);
    let setup = GKRSetup::construct(
        &table_driver,
        &decoder_table_data,
        1 << C::DOMAIN_SIZE_LOG2,
        &circuit,
    );

    let mut witness_gen_data = Vec::new_in(A::default());
    for el in decoder_table_data.iter() {
        let t = el.as_ref().copied().unwrap_or(Default::default());
        witness_gen_data.push(t);
    }

    let witness_eval_fn = witness_eval_fn.map(|el| UnrolledCircuitWitnessEvalFn::Memory {
        witness_fn: el,
        decoder_table: decoder_table_data.to_vec_in(A::default()),
    });

    CircuitSetup {
        family_idx: C::CIRCUIT_FAMILY,
        trace_len: 1 << C::DOMAIN_SIZE_LOG2,
        compiled_circuit: circuit,
        table_driver,
        setup,
        witness_eval_fn,
    }
}

use prover::definitions::DEFAULT_CAP_SIZE;

/// Per-program setup-params map, keyed by circuit family index. The recursion
/// drivers and the full-statement verifier both consume the caps in this
/// (ascending-key) order.
pub type Setups = std::collections::BTreeMap<u32, UnrolledCircuitSetupParams>;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct UnrolledCircuitSetupParams {
    pub family_idx: u32,
    pub capacity: u32,
    // #[serde(with = "serde_big_array::BigArray")]
    // #[serde(bound(deserialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Serialize"))]
    pub setup_caps: MerkleTreeCap<DEFAULT_CAP_SIZE>,
}

impl UnrolledCircuitSetupParams {
    /// Build the params from a committed setup tree's cap, converting the
    /// var-length cap into the fixed [`DEFAULT_CAP_SIZE`] one.
    ///
    /// # Panics
    /// If the cap does not have exactly [`DEFAULT_CAP_SIZE`] leafs.
    #[must_use]
    pub fn from_setup_tree_cap(
        family_idx: u32,
        capacity: u32,
        cap: prover::merkle_trees::MerkleTreeCapVarLength,
    ) -> Self {
        let num_leafs = cap.cap.len();
        Self {
            family_idx,
            capacity,
            setup_caps: MerkleTreeCap {
                cap: cap.cap.try_into().unwrap_or_else(|_| {
                    panic!("setup tree cap has {num_leafs} leafs, expected {DEFAULT_CAP_SIZE}")
                }),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DelegationCircuitSetupParams {
    pub delegation_type: u32,
    pub capacity: u32,
    // #[serde(with = "serde_big_array::BigArray")]
    // #[serde(bound(deserialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Serialize"))]
    pub setup_caps: MerkleTreeCap<DEFAULT_CAP_SIZE>,
}

pub fn compute_setup_commitment(
    setup: GKRSetup<BabyBearField>,
    cap_size: usize,
    lde_factor: usize,
    worker: &Worker,
) -> MerkleTreeCapVarLength {
    assert!(lde_factor.is_power_of_two());

    todo!();
}

pub fn binary_u8_to_u32(binary_u8: &[u8]) -> Vec<u32> {
    assert_eq!(binary_u8.len() % core::mem::size_of::<u32>(), 0);
    let mut binary = Vec::with_capacity(binary_u8.len() / core::mem::size_of::<u32>());
    for el in binary_u8.as_chunks::<4>().0 {
        binary.push(u32::from_le_bytes(*el));
    }
    binary
}

pub fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
    use std::io::Read;
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    let binary = binary_u8_to_u32(&buffer);
    (buffer, binary)
}

pub fn read_and_pad_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
    let (mut buffer, mut binary) = read_binary(path);
    pad_bytecode_bytes_for_proving(&mut buffer);
    pad_bytecode_for_proving(&mut binary);
    (buffer, binary)
}

pub fn pad_binary(mut buffer: Vec<u8>) -> (Vec<u8>, Vec<u32>) {
    let mut binary = binary_u8_to_u32(&buffer);
    pad_bytecode_bytes_for_proving(&mut buffer);
    pad_bytecode_for_proving(&mut binary);
    (buffer, binary)
}
