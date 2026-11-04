use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::cs::definitions::TimestampData;
use rand::rngs::StdRng;
use rand::seq::IndexedRandom;
use rand::RngExt;
use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::MEM_LOAD_TRACE_DATA_MARKER;
use riscv_transpiler::machine_mode_only_unrolled::MEM_STORE_TRACE_DATA_MARKER;

use crate::prover::mutations::buffer_delete_row::BufferDeleteRowMutator;
use crate::prover::mutations::buffer_duplicate_row::BufferDuplicateRowMutator;
use crate::prover::mutations::buffer_insert_clone_row::BufferInsertCloneRowMutator;
use crate::prover::mutations::buffer_swap_rows::BufferSwapRowsMutator;
use crate::prover::mutations::cycle_timestamp_mutator::CycleTimestampMutator;
use crate::prover::mutations::decoder_entry_mutator::DecoderEntryMutator;
use crate::prover::mutations::decoder_row_swap_mutator::DecoderRowSwapMutator;
use crate::prover::mutations::initial_pc_mutator::InitialPcMutator;
use crate::prover::mutations::mem_discr_flip_mutator::MemDiscrFlipMutator;
use crate::prover::mutations::read_timestamp_mutator::ReadTimestampMutator;
use crate::prover::mutations::trace_value_mutator::TraceValueMutator;
use crate::prover::seeds::SeedCase;
use crate::prover::seeds::StoredProofInputs;
use crate::prover::SeedCaseRef;
use crate::rv32im::prover::circuits::ProofInputs;
use crate::utils::env_conf;

mod buffer_delete_row;
mod buffer_duplicate_row;
mod buffer_insert_clone_row;
mod buffer_swap_rows;
mod cycle_timestamp_mutator;
mod decoder_entry_mutator;
mod decoder_row_swap_mutator;
mod initial_pc_mutator;
mod mem_discr_flip_mutator;
mod read_timestamp_mutator;
mod trace_value_mutator;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct MutationRecord {
    summary: String,
}

impl MutationRecord {
    pub fn summary(&self) -> &str {
        &self.summary
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct MutatedInput {
    pub original: SeedCaseRef,
    pub mutated_input: StoredProofInputs,
    pub mutations: Vec<MutationRecord>,
}

impl MutatedInput {
    pub fn new(seed: &SeedCase, mutated_input: StoredProofInputs, descr: &str) -> Self {
        Self {
            original: SeedCaseRef {
                seed_program: seed.seed_program.clone(),
                circuit: seed.circuit,
            },
            mutated_input,
            mutations: vec![MutationRecord {
                summary: descr.to_owned(),
            }],
        }
    }
}

impl PartialEq<&SeedCase> for MutatedInput {
    fn eq(&self, other: &&SeedCase) -> bool {
        self.mutated_input == other.base_input
    }
}

pub trait Mutator {
    fn name(&self) -> &'static str;

    fn mutate(&self, seed_case: &SeedCase, rng: &mut StdRng) -> MutatedInput {
        let mut mutated = seed_case.base_input.clone();
        self.mutate_input(&mut mutated, rng);
        MutatedInput::new(seed_case, mutated, self.name())
    }

    fn mutate_input(&self, input: &mut StoredProofInputs, rng: &mut StdRng) {
        match input {
            StoredProofInputs::AddSubLuiAuipcMop(proof_inputs)
            | StoredProofInputs::JumpBranchSlt(proof_inputs)
            | StoredProofInputs::XorAndOrShiftCsr(proof_inputs)
            | StoredProofInputs::MulDiv(proof_inputs) => {
                self.mutate_non_mem_inputs(proof_inputs, rng)
            }

            StoredProofInputs::LoadStore(proof_inputs, _)
            | StoredProofInputs::SubwordLoadStore(proof_inputs, _) => {
                self.mutate_mem_inputs(proof_inputs, rng)
            }

            StoredProofInputs::InitsAndTeardowns(_) => {}
            StoredProofInputs::BlakeDelegation(_) => {}
            StoredProofInputs::KeccakDelegation(_) => {}
        };
    }

    fn mutate_non_mem_inputs(
        &self,
        input: &mut ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    );

    fn mutate_mem_inputs(
        &self,
        input: &mut ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        rng: &mut StdRng,
    );
}

pub struct MutatorRegistry {
    mutators: Vec<Box<dyn Mutator>>,
    /// The maximum number of mutations that are applied to a sample.
    max_mutations: usize,
}

impl MutatorRegistry {
    pub fn new() -> Self {
        Self {
            mutators: vec![
                Box::new(BufferSwapRowsMutator),
                Box::new(BufferDuplicateRowMutator),
                Box::new(BufferDeleteRowMutator),
                Box::new(BufferInsertCloneRowMutator),
                Box::new(CycleTimestampMutator),
                Box::new(ReadTimestampMutator),
                Box::new(InitialPcMutator),
                Box::new(TraceValueMutator),
                Box::new(MemDiscrFlipMutator),
                Box::new(DecoderEntryMutator),
                Box::new(DecoderRowSwapMutator),
            ],
            max_mutations: env_conf("MAX_MUTATIONS", 1),
        }
    }

    /// Chooses a mutator from the registry at random.
    pub fn choose(&self, rng: &mut StdRng) -> &dyn Mutator {
        self.mutators
            .choose(rng)
            .map(|b| b.as_ref())
            .expect("registry not empty")
    }

    /// Randomly applies one or more mutations to an input.
    pub fn apply_mutations(&self, seed_case: &SeedCase, rng: &mut StdRng) -> MutatedInput {
        let range = 1..=self.max_mutations;
        assert!(!range.is_empty(), "max_mutations < 1");
        let count = rng.random_range(range);
        // count is at least 1 so we apply the first mutation and then we apply count-1 mutations
        // to the mutated output.
        let mut mutated_input = self.choose(rng).mutate(seed_case, rng);
        for _ in 0..(count - 1) {
            let mutator = self.choose(rng);
            mutator.mutate_input(&mut mutated_input.mutated_input, rng);
            mutated_input.mutations.push(MutationRecord {
                summary: mutator.name().to_owned(),
            })
        }
        assert_eq!(mutated_input.mutations.len(), count);
        mutated_input
    }
}

pub(crate) fn mutate_u32(value: &mut u32, rng: &mut StdRng) {
    match rng.random_range(0..6) {
        0 => {
            let bit = rng.random_range(0..u32::BITS);
            *value ^= 1u32 << bit;
        }
        1 => *value = value.wrapping_add(1),
        2 => *value = value.wrapping_sub(1),
        3 => {
            let delta = rng.random_range(1..=16);
            if rng.random_bool(0.5) {
                *value = value.wrapping_add(delta);
            } else {
                *value = value.wrapping_sub(delta);
            }
        }
        4 => *value = 0,
        5 => *value = u32::MAX,
        _ => unreachable!(),
    }
}

pub(crate) fn mutate_u16(value: &mut u16, rng: &mut StdRng) {
    match rng.random_range(0..6) {
        0 => {
            let bit = rng.random_range(0..u16::BITS);
            *value ^= 1u16 << bit;
        }
        1 => *value = value.wrapping_add(1),
        2 => *value = value.wrapping_sub(1),
        3 => {
            let delta = rng.random_range(1..=16) as u16;
            if rng.random_bool(0.5) {
                *value = value.wrapping_add(delta);
            } else {
                *value = value.wrapping_sub(delta);
            }
        }
        4 => *value = 0,
        5 => *value = u16::MAX,
        _ => unreachable!(),
    }
}

pub(crate) fn mutate_u8(value: &mut u8, rng: &mut StdRng) {
    match rng.random_range(0..6) {
        0 => {
            let bit = rng.random_range(0..u8::BITS);
            *value ^= 1u8 << bit;
        }
        1 => *value = value.wrapping_add(1),
        2 => *value = value.wrapping_sub(1),
        3 => {
            let delta = rng.random_range(1..=8) as u8;
            if rng.random_bool(0.5) {
                *value = value.wrapping_add(delta);
            } else {
                *value = value.wrapping_sub(delta);
            }
        }
        4 => *value = 0,
        5 => *value = u8::MAX,
        _ => unreachable!(),
    }
}

pub(crate) fn mutate_bool(value: &mut bool) {
    *value = !*value;
}

pub(crate) fn mutate_option_u8(value: &mut Option<u8>, rng: &mut StdRng) {
    match value {
        Some(inner) => match rng.random_range(0..3) {
            0 => mutate_u8(inner, rng),
            1 => *value = None,
            2 => *inner = rng.random(),
            _ => unreachable!(),
        },
        None => *value = Some(rng.random()),
    }
}

pub(crate) fn mutate_timestamp(value: &mut TimestampData, rng: &mut StdRng) {
    let mut scalar = value.as_scalar();
    match rng.random_range(0..6) {
        0 => {
            let bit = rng.random_range(0..48);
            scalar ^= 1u64 << bit;
        }
        1 => scalar = scalar.wrapping_add(1),
        2 => scalar = scalar.wrapping_sub(1),
        3 => {
            let delta = rng.random_range(1..=32);
            if rng.random_bool(0.5) {
                scalar = scalar.wrapping_add(delta);
            } else {
                scalar = scalar.wrapping_sub(delta);
            }
        }
        4 => scalar = 0,
        5 => scalar = u32::MAX as u64,
        _ => unreachable!(),
    }
    *value = TimestampData::from_scalar(scalar);
}

pub(crate) fn choose_distinct_indices(len: usize, rng: &mut StdRng) -> Option<(usize, usize)> {
    if len < 2 {
        return None;
    }

    let first = rng.random_range(0..len);
    let mut second = rng.random_range(0..(len - 1));
    if second >= first {
        second += 1;
    }

    Some((first, second))
}

pub(crate) fn choose_row_mut<'a, T>(buffer: &'a mut [T], rng: &mut StdRng) -> Option<&'a mut T> {
    if buffer.is_empty() {
        return None;
    }

    let idx = rng.random_range(0..buffer.len());
    Some(&mut buffer[idx])
}

pub(crate) fn mutate_decoder_entry(entry: &mut ExecutorFamilyDecoderData, rng: &mut StdRng) {
    match rng.random_range(0..8) {
        0 => mutate_u32(&mut entry.imm, rng),
        1 => mutate_u8(&mut entry.rs1_index, rng),
        2 => mutate_u8(&mut entry.rs2_index, rng),
        3 => {
            mutate_u8(&mut entry.rd_index, rng);
            entry.rd_is_zero = entry.rd_index == 0;
        }
        4 => mutate_bool(&mut entry.rd_is_zero),
        5 => mutate_u8(&mut entry.funct3, rng),
        6 => mutate_option_u8(&mut entry.funct7, rng),
        7 => mutate_u32(&mut entry.opcode_family_bits, rng),
        _ => unreachable!(),
    }
}

pub(crate) fn mutate_decoder_row(input: &mut Vec<ExecutorFamilyDecoderData>, rng: &mut StdRng) {
    if let Some(entry) = choose_row_mut(input.as_mut_slice(), rng) {
        mutate_decoder_entry(entry, rng);
    }
}

pub(crate) fn mutate_non_mem_trace_row(
    row: &mut NonMemoryOpcodeTracingDataWithTimestamp,
    rng: &mut StdRng,
) {
    match rng.random_range(0..6) {
        0 => mutate_u32(&mut row.opcode_data.rs1_value, rng),
        1 => mutate_u32(&mut row.opcode_data.rs2_value, rng),
        2 => mutate_u32(&mut row.opcode_data.rd_old_value, rng),
        3 => mutate_u32(&mut row.opcode_data.rd_value, rng),
        4 => mutate_u32(&mut row.opcode_data.new_pc, rng),
        5 => mutate_u16(&mut row.opcode_data.delegation_type, rng),
        _ => unreachable!(),
    }
}

pub(crate) fn mutate_mem_trace_row(
    row: &mut MemoryOpcodeTracingDataWithTimestamp,
    rng: &mut StdRng,
) {
    match row.discr {
        MEM_LOAD_TRACE_DATA_MARKER => match rng.random_range(0..4) {
            0 => mutate_u32(&mut row.opcode_data.rs1_value, rng),
            1 => mutate_u32(&mut row.opcode_data.aligned_ram_address, rng),
            2 => mutate_u32(&mut row.opcode_data.aligned_ram_read_value, rng),
            3 => {
                if rng.random_bool(0.5) {
                    mutate_u32(&mut row.opcode_data.rd_old_value, rng);
                } else {
                    mutate_u32(&mut row.opcode_data.rd_value, rng);
                }
            }
            _ => unreachable!(),
        },
        MEM_STORE_TRACE_DATA_MARKER => {
            let store_data: &mut riscv_transpiler::machine_mode_only_unrolled::StoreOpcodeTracingData =
                unsafe { core::mem::transmute(&mut row.opcode_data) };

            match rng.random_range(0..5) {
                0 => mutate_u32(&mut store_data.rs1_value, rng),
                1 => mutate_u32(&mut store_data.aligned_ram_address, rng),
                2 => mutate_u32(&mut store_data.rs2_value, rng),
                3 => mutate_u32(&mut store_data.aligned_ram_old_value, rng),
                4 => mutate_u32(&mut store_data.aligned_ram_write_value, rng),
                _ => unreachable!(),
            }
        }
        _ => mutate_u16(&mut row.discr, rng),
    }
}

pub(crate) fn flip_mem_discr(row: &mut MemoryOpcodeTracingDataWithTimestamp) {
    row.discr = match row.discr {
        MEM_LOAD_TRACE_DATA_MARKER => MEM_STORE_TRACE_DATA_MARKER,
        MEM_STORE_TRACE_DATA_MARKER => MEM_LOAD_TRACE_DATA_MARKER,
        _ => MEM_LOAD_TRACE_DATA_MARKER,
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn choose_distinct_indices_handles_short_inputs() {
        assert_eq!(
            choose_distinct_indices(0, &mut StdRng::seed_from_u64(1)),
            None
        );
        assert_eq!(
            choose_distinct_indices(1, &mut StdRng::seed_from_u64(1)),
            None
        );
    }

    #[test]
    fn choose_distinct_indices_returns_distinct_values() {
        let (a, b) = choose_distinct_indices(8, &mut StdRng::seed_from_u64(2)).unwrap();
        assert_ne!(a, b);
        assert!(a < 8);
        assert!(b < 8);
    }

    #[test]
    fn flip_mem_discr_toggles_between_known_variants() {
        let mut row = MemoryOpcodeTracingDataWithTimestamp {
            discr: MEM_LOAD_TRACE_DATA_MARKER,
            ..Default::default()
        };

        flip_mem_discr(&mut row);
        assert_eq!(row.discr, MEM_STORE_TRACE_DATA_MARKER);

        flip_mem_discr(&mut row);
        assert_eq!(row.discr, MEM_LOAD_TRACE_DATA_MARKER);
    }
}
