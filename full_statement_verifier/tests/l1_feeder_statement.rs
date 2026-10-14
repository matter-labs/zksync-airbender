//! Cheap typing and boundary checks of the L1 feeder statement. The
//! fixture-backed controls (delegation count words, setup-cap leaf flips)
//! live with the feeder-chain fixtures in `prover_pipeline`.

use full_statement_verifier::imports::unified_reduced_machine_sec_100 as standard;
use full_statement_verifier::imports::unified_reduced_machine_sec_100_l1_feeder as feeder;
use full_statement_verifier::unified_circuit_statement::{
    address_high_bits_shift, STANDARD_ADDRESS_HIGH_BITS_SHIFT, STANDARD_CYCLES_PER_INSTANCE,
};
use verifier_common::prover::definitions::DEFAULT_CAP_SIZE;

#[test]
fn feeder_verifier_geometry() {
    assert_eq!(feeder::TRACE_LEN_LOG2, 22);
    assert_eq!(feeder::CAP_SIZE, 32);
    assert_eq!(
        feeder::INIT_AND_TEARDOWN_SETS,
        standard::INIT_AND_TEARDOWN_SETS
    );
    assert_eq!(standard::TRACE_LEN_LOG2, 23);
    assert_eq!(DEFAULT_CAP_SIZE, 16);
}

/// The generated feeder verifier carries the configured query/PoW tuple,
/// and no PoW of a feeder proof (WHIR rounds, lookup challenges, batched
/// proximity, external challenges) exceeds the feeder PoW ceiling.
#[test]
fn feeder_pows_stay_under_the_ceiling() {
    use verifier_common::prover::gkr::prover_config::example_configs::{
        L1_FEEDER_MAX_POW_BITS, L1_FEEDER_QUERIES_AND_POW,
    };
    for (round, (queries, pow)) in L1_FEEDER_QUERIES_AND_POW.iter().enumerate() {
        assert_eq!(feeder::WHIR_QUERIES[round], *queries);
        assert_eq!(feeder::WHIR_POW_BITS[round], *pow);
    }
    let ceiling = L1_FEEDER_MAX_POW_BITS;
    assert!(feeder::WHIR_POW_BITS.iter().all(|pow| *pow <= ceiling));
    assert!(feeder::LOOKUP_CHALLENGES_POW_BITS <= ceiling);
    assert!(feeder::BATCHED_PROXIMITY_POW_BITS <= ceiling);
    assert!(verifier_common::MEMORY_DELEGATION_POW_BITS as u32 <= ceiling);
}

#[test]
fn feeder_instance_geometry_keeps_the_standard_address_ceiling() {
    assert_eq!(
        address_high_bits_shift(23),
        STANDARD_ADDRESS_HIGH_BITS_SHIFT
    );
    assert_eq!(address_high_bits_shift(feeder::TRACE_LEN_LOG2), 9);
    // MAX_TOP_BIT * window bytes: the same 2 GiB for both geometries
    for (trace_len_log2, shift) in [(23u32, 10u32), (22, 9)] {
        let max_top_bit = 1u64 << (32 - 16 - shift);
        let window_bytes = (1u64 << trace_len_log2) * 4;
        assert_eq!(max_top_bit * window_bytes, 1 << 31);
    }
    assert_eq!(STANDARD_CYCLES_PER_INSTANCE, 1 << 24);
    assert_eq!(1u64 << feeder::TRACE_LEN_LOG2, 1 << 22);
}

#[cfg(all(feature = "host_utils", feature = "verifiers"))]
#[test]
fn truncated_feeder_streams_are_rejected_at_the_checked_boundary() {
    use full_statement_verifier::host_utils::native_verify_unified_l1_feeder;
    // an empty stream and a stream that ends inside the setup cap
    for len in [0usize, 8, feeder::CAP_SIZE * 8 - 1] {
        let stream = vec![0u32; len];
        let err = native_verify_unified_l1_feeder(stream).unwrap_err();
        assert!(
            err.starts_with("unified l1 feeder statement rejected the stream"),
            "{err}"
        );
    }
}
