//! Reserve for partial circuits, one unpublished snapshot, unified tails and
//! init/teardown data. The pool needs one additional block to make progress.

use crate::ExecutionKind;
use common_constants::TimestampScalar;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::trace::PAGE_SIZE_LOG2;
use riscv_transpiler::jit::{
    max_counter_delta_per_snapshot, JitRunnerRam, DEFAULT_MAX_CYCLES_PER_SNAPSHOT,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};

fn stream<T>(circuit: CircuitType) -> (usize, usize) {
    (size_of::<T>(), circuit.get_domain_size())
}

/// Block size and RAM must pass configuration validation first.
pub(crate) fn producer_reserve_blocks(
    kind: ExecutionKind,
    block_bytes: usize,
    ram: JitRunnerRam,
) -> usize {
    use CircuitType::{Delegation, Unrolled};
    use UnrolledCircuitType::{Memory, NonMemory};
    let delegations = [
        stream::<Blake2sRoundFunctionDelegationWitness>(Delegation(
            DelegationCircuitType::Blake2WithCompression,
        )),
        stream::<BigintDelegationWitness>(Delegation(DelegationCircuitType::BigIntWithControl)),
        stream::<KeccakSpecial5DelegationWitness>(Delegation(
            DelegationCircuitType::KeccakSpecial5,
        )),
        stream::<Blake2sGFunctionDelegationWitness>(Delegation(
            DelegationCircuitType::Blake2GFunction,
        )),
    ];
    // Split tracing constructs all six ISA streams for every machine type.
    let split = [
        stream::<NonMemoryOpcodeTracingDataWithTimestamp>(Unrolled(NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        ))),
        stream::<NonMemoryOpcodeTracingDataWithTimestamp>(Unrolled(NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        ))),
        stream::<NonMemoryOpcodeTracingDataWithTimestamp>(Unrolled(NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        ))),
        stream::<NonMemoryOpcodeTracingDataWithTimestamp>(Unrolled(NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        ))),
        stream::<MemoryOpcodeTracingDataWithTimestamp>(Unrolled(Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        ))),
        stream::<MemoryOpcodeTracingDataWithTimestamp>(Unrolled(Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        ))),
    ];
    let unified = [stream::<UnifiedOpcodeTracingDataWithTimestamp>(Unrolled(
        UnrolledCircuitType::Unified,
    ))];
    let (isa_streams, carrier): (&[_], _) = match kind {
        ExecutionKind::Unrolled => (&split, UnrolledCircuitType::InitsAndTeardowns),
        ExecutionKind::Unified => (&unified, UnrolledCircuitType::Unified),
    };
    let snapshot_rows = max_counter_delta_per_snapshot(DEFAULT_MAX_CYCLES_PER_SNAPSHOT);
    let mut partial_blocks = 0;
    let mut snapshot_blocks_total = 0;
    for &(row_bytes, domain_size) in delegations.iter().chain(isa_streams) {
        let rows_per_block = block_bytes / row_bytes;
        partial_blocks += domain_size.div_ceil(rows_per_block);
        snapshot_blocks_total += snapshot_blocks(snapshot_rows, rows_per_block, domain_size);
    }

    let domain_size = carrier.get_domain_size();
    let sets = carrier.get_num_inits_and_teardowns_sets();
    let retained_unified_blocks = match kind {
        ExecutionKind::Unrolled => 0,
        ExecutionKind::Unified => {
            // These instances wait for the simulator's memory walk to supply I&T.
            let windows = (ram.ram_size() / size_of::<u32>()).div_ceil(domain_size);
            let max_instances = windows.div_ceil(sets);
            let rows_per_block = block_bytes / size_of::<UnifiedOpcodeTracingDataWithTimestamp>();
            max_instances * domain_size.div_ceil(rows_per_block)
        }
    };

    let page_size = 1 << PAGE_SIZE_LOG2;
    assert!(domain_size.is_multiple_of(page_size));
    let pages = sets * (domain_size / page_size);
    let packed_items = pages * page_size;
    let index_capacity = block_bytes / size_of::<u32>();
    // chunk_into_blocks rounds values and timestamps down to whole pages.
    let value_capacity = (index_capacity / page_size) * page_size;
    let timestamp_capacity = (block_bytes / size_of::<TimestampScalar>() / page_size) * page_size;
    let inits_and_teardowns_blocks = pages.div_ceil(index_capacity)
        + packed_items.div_ceil(value_capacity)
        + packed_items.div_ceil(timestamp_capacity);

    partial_blocks + snapshot_blocks_total + retained_unified_blocks + inits_and_teardowns_blocks
}

// A snapshot can start inside a block and cross circuit boundaries, each of
// which drains the producer's chunks. The extra terms cover that fragmentation.
fn snapshot_blocks(length: usize, rows_per_block: usize, domain_size: usize) -> usize {
    if length == 0 {
        0
    } else {
        length.div_ceil(rows_per_block) + length.div_ceil(domain_size) + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::min;

    #[test]
    fn production_geometry_reserves() {
        for (kind, ram, expected) in [
            (ExecutionKind::Unrolled, JitRunnerRam::Medium, 197),
            (ExecutionKind::Unrolled, JitRunnerRam::Full, 197),
            (ExecutionKind::Unified, JitRunnerRam::Medium, 220),
            (ExecutionKind::Unified, JitRunnerRam::Full, 604),
        ] {
            assert_eq!(producer_reserve_blocks(kind, 64 << 20, ram), expected);
        }
    }

    // Count allocations while filling blocks and draining at circuit boundaries.
    fn oracle_new_blocks(
        domain_size: usize,
        rows_per_block: usize,
        mut start: usize,
        initial_fill: usize,
        length: usize,
    ) -> usize {
        let end = start + length;
        let mut back_len = (initial_fill > 0).then_some(initial_fill);
        let mut allocations = 0;
        while start != end {
            let next_circuit_boundary = (start + 1).next_multiple_of(domain_size);
            if back_len.is_none_or(|len| len == rows_per_block) {
                allocations += 1;
                back_len = Some(0);
            }
            let len = back_len.unwrap();
            let spare_capacity = rows_per_block - len;
            let segment_end = min(end, next_circuit_boundary);
            let diff = min(spare_capacity, segment_end - start);
            assert_ne!(diff, 0);
            back_len = Some(len + diff);
            start += diff;
            if start.is_multiple_of(domain_size) {
                back_len = None;
            }
        }
        allocations
    }

    #[test]
    fn snapshot_bound_holds_against_the_producer_allocation_oracle() {
        for domain_size in 1..=16usize {
            for rows_per_block in 1..=8usize {
                for start in 0..domain_size {
                    for initial_fill in 0..=rows_per_block {
                        for length in 0..=2 * domain_size + 1 {
                            let bound = snapshot_blocks(length, rows_per_block, domain_size);
                            let actual = oracle_new_blocks(
                                domain_size,
                                rows_per_block,
                                start,
                                initial_fill,
                                length,
                            );
                            assert!(
                                actual <= bound,
                                "D={domain_size} q={rows_per_block} start={start} \
                                 fill={initial_fill} L={length}: {actual} > {bound}"
                            );
                        }
                    }
                }
            }
        }
    }
}
