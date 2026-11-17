use prover::gkr::prover_config::{example_configs::l1_wrap, ProverConfig};
use verifier_evm::generator::WhirGenConfig;

fn candidate() -> ProverConfig {
    let mut config = l1_wrap::packed_prover_config();
    config.whir_schedule.base_round.folding_pow_bits = 9;
    for (i, round) in config.whir_schedule.internal_rounds.iter_mut().enumerate() {
        round.lde_factor_log2 = [8, 12, 17, 21][i];
        round.folding_log2 = [4, 5, 4, 4][i];
        round.num_queries = [11, 7, 5, 4][i];
        round.queries_pow_bits = [27, 30, 30, 30][i];
        round.folding_pow_bits = 9;
        round.num_ood_samples = 1;
        round.ood_pow_bits = [16, 20, 25, 29][i];
    }
    config
}

#[test]
fn canonical_l1_wrap_schedule() {
    let config = l1_wrap::packed_prover_config();
    config.validate_for_whir_message_size(24);
    let schedule = &config.whir_schedule;
    assert_eq!(schedule, &candidate().whir_schedule);
    assert_eq!(schedule.fold_steps(), [1, 4, 5, 4, 4]);
    assert_eq!(schedule.queries_per_round(), [12, 11, 7, 5, 4]);
    assert_eq!(schedule.queries_pow_bits_per_round(), [30, 27, 30, 30, 30]);
    assert_eq!(
        schedule
            .base_round
            .batching_pow_bits::<field::Proth120, field::Proth120>(100, 24, 14),
        13
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
    assert_eq!(derived.codeword_log2, 31);
    assert_eq!(derived.rfin, 6);
    let regions = derived.memory_regions();
    let size = |name| regions.iter().find(|(n, _, _)| *n == name).unwrap().1.value;
    assert_eq!(size("FBUF_PTR"), 32 * 32);
    assert!(!regions.iter().any(|(name, _, _)| *name == "OOD_PTR"));
    assert_eq!(size("POW_PTR"), (12 + 11 + 7 + 5 + 4) * 96);
    let switch = derived.schedule_switch_yul();
    assert!(switch.contains("fold_pow_bits := 9"));
    assert!(switch.contains("ood_pow_bits := 16"));
}

#[test]
fn legacy_plain_challenges_remain_supported() {
    let mut config = candidate();
    config.whir_schedule.base_round.folding_pow_bits = 0;
    for round in &mut config.whir_schedule.internal_rounds {
        round.folding_pow_bits = 0;
        round.ood_pow_bits = 0;
    }
    let derived = WhirGenConfig::derive(&config, 96, 10);
    assert!(derived.schedule_switch_yul().contains("fold_pow_bits := 0"));
}

#[test]
#[should_panic(expected = "exactly one OOD sample")]
fn multiple_ood_samples_are_rejected() {
    let mut config = candidate();
    config.whir_schedule.internal_rounds[0].num_ood_samples = 2;
    WhirGenConfig::derive(&config, 96, 10);
}

#[test]
#[should_panic(expected = "folding PoW exceeds cap")]
fn folding_pow_above_cap_is_rejected() {
    let mut config = candidate();
    config.whir_schedule.internal_rounds[1].folding_pow_bits = l1_wrap::MAX_POW_BITS + 1;
    WhirGenConfig::derive(&config, 96, 10);
}

#[test]
#[should_panic(expected = "OOD PoW exceeds cap")]
fn ood_pow_above_cap_is_rejected() {
    let mut config = candidate();
    config.whir_schedule.internal_rounds[0].ood_pow_bits = l1_wrap::MAX_POW_BITS + 1;
    WhirGenConfig::derive(&config, 96, 10);
}
