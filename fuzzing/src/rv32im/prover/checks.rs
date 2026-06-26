use prover::common_constants::TimestampScalar;
use prover::common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use prover::common_constants::INITIAL_TIMESTAMP;
use prover::common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;
use prover::common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
use prover::common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;
use prover::common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX;
use prover::common_constants::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;
use prover::field::Field as _;
use prover::field::Mersenne31Quartic;
use riscv_transpiler::vm::Counters as _;
use riscv_transpiler::vm::DelegationsAndFamiliesCounters;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::NUM_CYCLES_PER_CHUNK;

pub fn validate_counters(counters: &DelegationsAndFamiliesCounters) {
    assert!(
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<MUL_DIV_CIRCUIT_FAMILY_IDX>() < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
}

pub fn validate_sets(r: &ReadSets, w: &WriteSets) {
    for (pc, ts) in w.write_set().iter().copied() {
        if !r.read_set().contains(&(pc, ts)) {
            panic!("read set doesn't contain a pair {:?}", (pc, ts));
        }
    }

    for (pc, ts) in r.read_set().iter().copied() {
        if !w.write_set().contains(&(pc, ts)) {
            panic!("write set doesn't contain a pair {:?}", (pc, ts));
        }
    }
}

pub fn validate_inits_and_teardowns(
    read_sets: &ReadSets,
    write_sets: &WriteSets,
    flattened_inits_and_teardowns: &[(u32, (TimestampScalar, u32))],
    accumulators: &Accumulators,
    total_unique_teardowns: usize,
) {
    let expected_init_set: Vec<_> = read_sets
        .memory_read_set()
        .difference(write_sets.memory_write_set())
        .collect();
    let expected_teardown_set: Vec<_> = write_sets
        .memory_write_set()
        .difference(read_sets.memory_read_set())
        .collect();
    assert_eq!(expected_init_set.len(), expected_teardown_set.len());
    // assert_eq!(expected_init_set.len(), flattened_inits_and_teardowns.len());

    if flattened_inits_and_teardowns.len() != expected_init_set.len() {
        for (address, (teardown_ts, teardown_value)) in flattened_inits_and_teardowns.iter() {
            let mut init_set_el = None;
            for (is_reg, addr, ts, init_value) in expected_init_set.iter() {
                if *addr == *address {
                    init_set_el = Some((*is_reg, *addr, *ts, *init_value));
                }
            }
            let Some(_init_set_el) = init_set_el else {
                panic!(
                    "No expected init set element for address {} of flattened inits or teardowns",
                    *address
                );
            };

            let mut teardown_set_el = None;
            for (is_reg, addr, ts, teardown_value) in expected_teardown_set.iter() {
                if *addr == *address {
                    teardown_set_el = Some((*is_reg, *addr, *ts, *teardown_value));
                }
            }
            let Some(teardown_set_el) = teardown_set_el else {
                panic!("No expected teardown set element for address {} of flattened inits or teardowns", *address);
            };
            let (_, _, expected_teardown_ts, expected_teardown_value) = teardown_set_el;
            assert_eq!(
                *teardown_ts, expected_teardown_ts,
                "failed for address {}",
                address
            );
            assert_eq!(
                *teardown_value, expected_teardown_value,
                "failed for address {}",
                address
            );
        }
    }

    for (idx, (is_register, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
        assert!(
            !*is_register,
            "found an unexpected init for register {} with value {} at timestamp {}",
            *addr, *init_value, *ts
        );
        assert_eq!(
            *ts, 0,
            "init timestamp is invalid for memory address {}",
            addr
        );
        assert_eq!(
            *init_value, 0,
            "init value is invalid for memory address {}",
            addr
        );
        assert_eq!(
            flattened_inits_and_teardowns[idx].0, *addr,
            "diverged at expected lazy init {}",
            idx
        );
    }
    for (idx, (is_register, addr, ts, value)) in expected_teardown_set.iter().enumerate() {
        assert!(
            !*is_register,
            "found an unexpected teardown for register {} with value {} at timestamp {}",
            *addr, *value, *ts
        );
        assert!(
            *ts > INITIAL_TIMESTAMP,
            "teardown timestamp is invalid for memory address {}",
            addr
        );
        assert_eq!(
            flattened_inits_and_teardowns[idx].1 .0, *ts,
            "diverged at expected lazy init {}",
            idx
        );
        assert_eq!(
            flattened_inits_and_teardowns[idx].1 .1, *value,
            "diverged at expected lazy init {}",
            idx
        );
    }

    for ((_, addr0, _, _), (_, addr1, _, _)) in
        expected_init_set.iter().zip(expected_teardown_set.iter())
    {
        assert_eq!(*addr0, *addr1);
    }

    assert_eq!(total_unique_teardowns, expected_teardown_set.len());

    assert_eq!(accumulators.permutation_argument(), Mersenne31Quartic::ONE);
    assert_eq!(accumulators.delegation_argument(), Mersenne31Quartic::ZERO);
}
