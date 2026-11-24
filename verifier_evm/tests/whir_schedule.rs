use prover::gkr::prover_config::{example_configs::l1_wrap, ProverConfig};
use verifier_evm::generator::WhirGenConfig;

fn candidate() -> ProverConfig {
    let mut config = l1_wrap::packed_prover_config();
    let base = &mut config.whir_schedule.base_round;
    base.lde_factor_log2 = 8;
    base.num_queries = 11;
    base.queries_pow_bits = 27;
    base.folding_pow_bits = 10;
    for (i, round) in config.whir_schedule.internal_rounds.iter_mut().enumerate() {
        round.lde_factor_log2 = [9, 12, 17, 21][i];
        round.folding_log2 = [4, 4, 4, 5][i];
        round.num_queries = [10, 7, 5, 4][i];
        round.queries_pow_bits = [25, 30, 30, 30][i];
        round.folding_pow_bits = [10, 9, 10, 10][i];
        round.num_ood_samples = 1;
        round.ood_pow_bits = [18, 20, 26, 30][i];
    }
    config
}

#[test]
fn canonical_pessimistic_l1_schedule() {
    let config = l1_wrap::packed_prover_config();
    config.validate_for_whir_message_size(24);
    let schedule = &config.whir_schedule;
    assert_eq!(schedule, &candidate().whir_schedule);
    assert_eq!(schedule.fold_steps(), [1, 4, 4, 4, 5]);
    assert_eq!(schedule.queries_per_round(), [11, 10, 7, 5, 4]);
    assert_eq!(schedule.queries_pow_bits_per_round(), [27, 25, 30, 30, 30]);
    assert_eq!(
        schedule
            .base_round
            .batching_pow_bits::<field::Proth120, field::Proth120>(100, 24, 14),
        14
    );
    eprintln!(
        "L1_WHIR_CONFIG={}",
        serde_json::to_string(schedule).unwrap()
    );
}

#[test]
fn folding_and_ood_pow_geometry() {
    let config = candidate();
    config.validate_for_whir_message_size(24);
    let derived = WhirGenConfig::derive(&config, 96, 10);
    assert_eq!(derived.base_domain_log2, 32);
    assert_eq!(derived.rfin, 6);
    let regions = derived.memory_regions();
    let size = |name| regions.iter().find(|(n, _, _)| *n == name).unwrap().1.value;
    assert_eq!(size("FBUF_PTR"), 32 * 32);
    assert!(!regions.iter().any(|(name, _, _)| *name == "OOD_PTR"));
    assert_eq!(
        size("POW_PTR"),
        ((11 + 1) + (10 + 1) + (7 + 1) + (5 + 1)) * 96
    );
    let switch = derived.schedule_switch_yul();
    assert!(switch.contains("fold_pow_bits := 10"));
    assert!(switch.contains("ood_pow_bits := 18"));
}

#[test]
fn zero_pow_schedule_renders_plain_challenges() {
    let mut config = candidate();
    config.whir_schedule.base_round.folding_pow_bits = 0;
    for round in &mut config.whir_schedule.internal_rounds {
        round.folding_pow_bits = 0;
        round.ood_pow_bits = 0;
    }
    let derived = WhirGenConfig::derive(&config, 96, 10);
    let switch = derived.schedule_switch_yul();
    assert_eq!(
        switch.matches("fold_pow_bits := 0 ").count(),
        derived.num_rounds
    );
    assert_eq!(
        switch.matches("ood_pow_bits := 0 ").count(),
        derived.num_rounds
    );
}

#[test]
#[should_panic(expected = "exactly one OOD sample")]
fn multiple_ood_samples_are_rejected() {
    let mut config = candidate();
    config.whir_schedule.internal_rounds[0].num_ood_samples = 2;
    WhirGenConfig::derive(&config, 96, 10);
}

#[test]
#[should_panic(expected = "folding PoW 65 exceeds")]
fn folding_pow_above_cap_is_rejected() {
    let mut config = candidate();
    config.whir_schedule.internal_rounds[1].folding_pow_bits = 65;
    WhirGenConfig::derive(&config, 96, 10);
}

#[test]
#[should_panic(expected = "OOD PoW 65 exceeds")]
fn ood_pow_above_cap_is_rejected() {
    let mut config = candidate();
    config.whir_schedule.internal_rounds[0].ood_pow_bits = 65;
    WhirGenConfig::derive(&config, 96, 10);
}

#[test]
fn mixed_oracle_domains_accept_nonce_width_pow() {
    let mut config = candidate();
    let schedule = &mut config.whir_schedule;
    schedule.base_round.queries_pow_bits = 64;
    schedule.base_round.folding_pow_bits = 64;
    schedule.internal_rounds[0].ood_pow_bits = 64;

    let derived = WhirGenConfig::derive(&config, 96, 10);
    let query_bits: Vec<_> = (0..derived.num_rounds)
        .map(|round| derived.qib(round))
        .collect();
    assert_eq!(query_bits, [31, 28, 27, 28, 27]);
    let switch = derived.schedule_switch_yul();
    assert!(switch.contains("pow_bits := 64"));
    assert!(switch.contains("fold_pow_bits := 64"));
    assert!(switch.contains("ood_pow_bits := 64"));
    assert!(switch.contains("qib := 28 vp := 16 cb := 9"));
}

#[test]
fn ethproofs_wrap_keeps_the_base_domain_for_two_internal_oracles() {
    let config = l1_wrap::ethproofs_packed_prover_config();
    let geometry = WhirGenConfig::derive(&config, 96, 10);
    assert_eq!(geometry.base_domain_log2, 32);
    assert_eq!(geometry.rfin, 7);
    let query_bits: Vec<_> = (0..geometry.num_rounds).map(|r| geometry.qib(r)).collect();
    assert_eq!(query_bits, [31, 31, 28, 25, 23, 20]);
    let schedule = geometry.schedule_switch_yul();
    for (qib, coset_bits) in query_bits.into_iter().zip([7, 8, 9, 10, 12, 13]) {
        assert!(schedule.contains(&format!("qib := {qib} vp :=")));
        assert!(schedule.contains(&format!(" cb := {coset_bits} }}")));
    }
}
