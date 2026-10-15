#![feature(allocator_api)]

use crate::cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::TableDriver;
use definitions::MerkleTreeCap;
use merkle_trees::DefaultTreeConstructor;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::fft::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::*;
use prover::merkle_trees::MerkleTreeCapVarLength;
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
pub use ::unified_reduced_machine::UnifiedReducedMachineCircuit;
pub use ::unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22;

pub use ::bigint_with_control::BigIntDelegationCircuit;
pub use ::blake2_g_function::Blake2sGFunctionDelegationCircuit;
pub use ::blake2_with_compression::Blake2sWithCompressionDelegationCircuit;
pub use ::keccak_chi5::KeccakChi5DelegationCircuit;
pub use ::keccak_column_parity::KeccakColumnParityDelegationCircuit;
pub use ::keccak_special5::KeccakSpecial5DelegationCircuit;
pub use ::keccak_theta_rho::KeccakThetaRhoDelegationCircuit;

pub use ::inits_and_teardowns;

pub use bigint_with_control;
pub use blake2_g_function;
pub use blake2_with_compression;
pub use keccak_chi5;
pub use keccak_column_parity;
pub use keccak_special5;
pub use keccak_theta_rho;
pub use prover;

pub mod circuits;
pub mod program_setups;
pub mod unrolled_circuits;
pub use self::circuits::*;
pub use self::unrolled_circuits::*;

pub fn pad_bytecode_bytes_for_proving(bytecode: &mut Vec<u8>) {
    pad_bytecode_bytes_for_proving_with_rom(bytecode, common_constants::REGULAR_ROM);
}

pub fn pad_bytecode_for_proving(bytecode: &mut Vec<u32>) {
    pad_bytecode_for_proving_with_rom(bytecode, common_constants::REGULAR_ROM);
}

pub fn pad_bytecode_bytes_for_proving_with_rom(
    bytecode: &mut Vec<u8>,
    rom: common_constants::RomGeometry,
) {
    assert!(
        bytecode.len() <= rom.byte_size(),
        "bytecode exceeds selected ROM"
    );
    bytecode.resize(rom.byte_size(), 0);
}

pub fn pad_bytecode_for_proving_with_rom(
    bytecode: &mut Vec<u32>,
    rom: common_constants::RomGeometry,
) {
    assert!(
        bytecode.len() <= rom.word_size(),
        "bytecode exceeds selected ROM"
    );
    bytecode.resize(rom.word_size(), 0);
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
        decoder_table_data,
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
        decoder_table_data,
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

/// The setup caps a profile commits: [`DEFAULT_CAP_SIZE`] leaves for
/// `Standard`, the feeder config's cap for `L1Feeder`. Every leaf is part of
/// the statement (the verifier stream and `end_params`); the entry point
/// fixes the cap, so no cap-length word enters the stream.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct UnrolledCircuitSetupParams {
    pub family_idx: u32,
    pub capacity: u32,
    pub setup_caps: MerkleTreeCapVarLength,
}

impl UnrolledCircuitSetupParams {
    /// Build the params from a committed setup tree's cap, which must have
    /// exactly `expected_cap_size` leaves (the trusted profile config's
    /// `cap_size`).
    ///
    /// # Panics
    /// If the cap does not have exactly `expected_cap_size` leaves.
    #[must_use]
    pub fn from_setup_tree_cap(
        family_idx: u32,
        capacity: u32,
        cap: prover::merkle_trees::MerkleTreeCapVarLength,
        expected_cap_size: usize,
    ) -> Self {
        let params = Self {
            family_idx,
            capacity,
            setup_caps: cap,
        };
        params
            .validate_cap_size(expected_cap_size)
            .unwrap_or_else(|err| panic!("{err}"));
        params
    }

    /// Repeat the constructor's shape check on deserialized params (serde
    /// bypasses [`Self::from_setup_tree_cap`]).
    pub fn validate_cap_size(&self, expected_cap_size: usize) -> Result<(), String> {
        let num_leafs = self.setup_caps.cap.len();
        if num_leafs != expected_cap_size {
            return Err(format!(
                "setup tree cap of family {} has {num_leafs} leafs, expected {expected_cap_size}",
                self.family_idx
            ));
        }
        Ok(())
    }

    /// The cap as the verifier stream consumes it: every leaf, in order.
    pub fn flattened_setup_caps(&self) -> &[u32] {
        self.setup_caps.cap.as_flattened()
    }
}

/// Every entry of `setups` must carry exactly `expected_cap_size` leaves.
pub fn validate_setups_cap_size(setups: &Setups, expected_cap_size: usize) -> Result<(), String> {
    for params in setups.values() {
        params.validate_cap_size(expected_cap_size)?;
    }
    Ok(())
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
    _setup: GKRSetup<BabyBearField>,
    _cap_size: usize,
    lde_factor: usize,
    _worker: &Worker,
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
    let mut file = std::fs::File::open(path)
        .map_err(|_| {
            panic!("Failed to load file at path {}", path.display());
        })
        .expect("must open provided file");
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
