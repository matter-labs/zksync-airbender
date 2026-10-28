use super::*;
use crate::definitions::SecurityLevel;
use crate::gkr::prover_config::{example_configs, WhirSchedule};

fn config(pack: usize, mode: CommitmentMode) -> ProverConfig {
    let mut config = ProverConfig::whir_only(
        16 - pack,
        WhirSchedule::from_legacy_arrays(2, 16, pack, &[4, 4], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    );
    config.commitment_mode = mode;
    config
}

fn geometry(
    config: &ProverConfig,
    widths: [usize; 3],
) -> Result<BaseCommitmentGeometry, CommitmentGeometryError> {
    BaseCommitmentGeometry::from_config(
        config,
        BaseColumns {
            memory: widths[0],
            witness: widths[1],
            setup: widths[2],
        },
    )
}

#[test]
fn separate_and_merged_sets_have_independent_golden_widths() {
    let separate = geometry(
        &config(2, CommitmentMode::SeparateMemoryAndWitness),
        [3, 3, 1],
    )
    .unwrap();
    let merged = geometry(
        &config(2, CommitmentMode::MergedMemoryAndWitness),
        [3, 3, 1],
    )
    .unwrap();
    assert_eq!(
        separate.logical_columns(),
        BaseColumns {
            memory: 3,
            witness: 3,
            setup: 1
        }
    );
    assert_eq!(merged.logical_columns(), separate.logical_columns());
    assert_eq!(
        separate.oracles().map(|o| (
            o.role(),
            o.logical_columns(),
            o.physical_columns(),
            o.padded_columns()
        )),
        [
            (BaseOracleRole::Memory, 3, 1, 4),
            (BaseOracleRole::Witness, 3, 1, 4),
            (BaseOracleRole::Setup, 1, 1, 4)
        ]
    );
    assert_eq!(
        merged.oracles().map(|o| (
            o.role(),
            o.logical_columns(),
            o.physical_columns(),
            o.padded_columns()
        )),
        [
            (BaseOracleRole::Memory, 6, 2, 8),
            (BaseOracleRole::Witness, 0, 0, 0),
            (BaseOracleRole::Setup, 1, 1, 4)
        ]
    );
    assert_eq!(
        geometry(
            &config(2, CommitmentMode::SeparateMemoryAndWitness),
            [1, 1, 1]
        )
        .unwrap()
        .total_physical_columns(),
        3
    );
    assert_eq!(
        geometry(
            &config(2, CommitmentMode::MergedMemoryAndWitness),
            [1, 1, 1]
        )
        .unwrap()
        .total_physical_columns(),
        2
    );
    assert_eq!(merged.oracle(BaseOracleRole::Witness).physical_columns(), 0);
}

#[test]
fn exact_tail_empty_and_identity_widths() {
    for pack in 0..=4 {
        let group = 1 << pack;
        for width in [0, 1, group - 1, group, group + 1, 2 * group + 1] {
            for mode in [
                CommitmentMode::SeparateMemoryAndWitness,
                CommitmentMode::MergedMemoryAndWitness,
            ] {
                let cfg = config(pack, mode);
                let shape = geometry(&cfg, [width, group, 0]).unwrap();
                assert_eq!(
                    shape.total_physical_columns(),
                    shape
                        .logical_columns()
                        .committed_polys(pack, cfg.merged_memory_and_witness())
                );
                for oracle in shape.oracles() {
                    assert_eq!(oracle.padded_columns(), oracle.physical_columns() * group);
                    assert!(oracle.padded_columns() >= oracle.logical_columns());
                    assert!(oracle.padded_columns() - oracle.logical_columns() < group);
                    if pack == 0 {
                        assert_eq!(oracle.logical_columns(), oracle.physical_columns());
                    }
                }
            }
        }
    }
    let shape = geometry(
        &config(2, CommitmentMode::SeparateMemoryAndWitness),
        [4, 5, 0],
    )
    .unwrap();
    assert_eq!(
        shape
            .oracles()
            .map(|o| (o.physical_columns(), o.padded_columns())),
        [(1, 4), (2, 8), (0, 0)]
    );
    assert_eq!(
        (
            shape.trace_len_log2(),
            shape.pack_log2(),
            shape.message_size_log2()
        ),
        (14, 2, 16)
    );
    assert_eq!(
        (
            shape.lde_factor(),
            shape.values_per_leaf(),
            shape.cap_size()
        ),
        (2, 16, 16)
    );
    assert_eq!(
        geometry(
            &config(4, CommitmentMode::MergedMemoryAndWitness),
            [0, 0, 0]
        )
        .unwrap()
        .total_physical_columns(),
        0
    );
}

#[test]
fn accepts_physical_targets_and_virtual_geometry() {
    for (trace, pack, widths, physical) in [
        (20, 4, [225, 538, 6], [15, 34, 1]),
        (23, 1, [38, 58, 10], [19, 29, 5]),
        (20, 2, [225, 538, 6], [57, 135, 2]),
    ] {
        let cfg = example_configs::packed_config_for_security_level_under_pessimistic_conjecture(
            trace,
            pack,
            SecurityLevel::Sec100,
        );
        cfg.validate_for_whir_message_size(trace + pack);
        let shape = geometry(&cfg, widths).unwrap();
        assert_eq!(shape.message_size_log2(), trace + pack);
        assert_eq!(shape.oracles().map(|o| o.physical_columns()), physical);
        assert!(!shape.is_virtual_packing());
    }
    for packing in [
        example_configs::BasePacking::VIRTUAL,
        example_configs::BasePacking::physical_and_virtual(2),
    ] {
        let trace = 22 - packing.physical_packing_log2;
        let cfg = example_configs::prover_config(
            example_configs::SoundnessMode::PessimisticConjecture,
            SecurityLevel::Sec100,
            trace,
            packing,
            None,
        );
        let shape = geometry(&cfg, [225, 538, 6]).unwrap();
        assert!(shape.is_virtual_packing());
        assert_eq!(
            (shape.message_size_log2(), shape.values_per_leaf()),
            (22, 1)
        );
    }
}

#[test]
fn geometry_is_independent_of_backend_field_and_protocol_feature_support() {
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.trace_len_log2 = 30;
    cfg.whir_schedule.base_round.folding_pow_bits = 7;
    let round = &mut cfg.whir_schedule.internal_rounds[0];
    round.num_ood_samples = 2;
    round.ood_pow_bits = 9;
    round.folding_pow_bits = 11;
    cfg.validate_for_whir_message_size(30);
    assert_eq!(geometry(&cfg, [1, 1, 1]).unwrap().message_size_log2(), 30);
}

#[test]
fn rejects_shifts_additions_products_and_merged_width_overflow() {
    for (trace, pack) in [
        (usize::MAX, 1),
        (16, usize::BITS as usize),
        (usize::BITS as usize, 0),
    ] {
        let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
        cfg.trace_len_log2 = trace;
        cfg.whir_schedule.base_round.physical_packing_log2 = pack;
        assert!(matches!(
            geometry(&cfg, [1, 1, 1]),
            Err(CommitmentGeometryError::Overflow { .. })
        ));
    }
    for widths in [[usize::MAX, 0, 0], [0, usize::MAX, 0], [0, 0, usize::MAX]] {
        assert!(matches!(
            geometry(&config(2, CommitmentMode::SeparateMemoryAndWitness), widths),
            Err(CommitmentGeometryError::Overflow { .. })
        ));
    }
    assert_eq!(
        geometry(
            &config(1, CommitmentMode::MergedMemoryAndWitness),
            [usize::MAX, 1, 0]
        ),
        Err(CommitmentGeometryError::Overflow {
            quantity: "merged columns"
        })
    );
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.whir_schedule.base_round.lde_factor_log2 = usize::BITS as usize - 1;
    assert_eq!(
        geometry(&cfg, [0, 0, 0]),
        Err(CommitmentGeometryError::Overflow {
            quantity: "LDE domain"
        })
    );
    let width = 1usize << (usize::BITS - 18);
    assert_eq!(
        geometry(
            &config(0, CommitmentMode::SeparateMemoryAndWitness),
            [width; 3]
        ),
        Err(CommitmentGeometryError::Overflow {
            quantity: "total LDE elements"
        })
    );
    for case in 0..3 {
        let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
        match case {
            0 => cfg.whir_schedule.base_round.fold_log2 = usize::MAX,
            1 => cfg.whir_schedule.base_round.lde_factor_log2 = usize::MAX,
            _ => cfg.whir_schedule.internal_rounds[0].lde_factor_log2 = usize::MAX,
        }
        assert!(matches!(
            geometry(&cfg, [1, 1, 1]),
            Err(CommitmentGeometryError::Overflow { .. })
        ));
    }
}

#[test]
fn rejects_invalid_caps_and_unit_lde() {
    for invalid in [0, 3, 6] {
        let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
        cfg.cap_size = invalid;
        assert_eq!(
            geometry(&cfg, [1, 1, 1]),
            Err(CommitmentGeometryError::InvalidPowerOfTwo {
                parameter: "cap size"
            })
        );
    }
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.whir_schedule.base_round.lde_factor_log2 = 0;
    assert_eq!(
        geometry(&cfg, [1, 1, 1]),
        Err(CommitmentGeometryError::InvalidLdeFactor {
            parameter: "LDE factor"
        })
    );
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.whir_schedule.internal_rounds[0].lde_factor_log2 = 0;
    assert_eq!(
        geometry(&cfg, [1, 1, 1]),
        Err(CommitmentGeometryError::InvalidLdeFactor {
            parameter: "intermediate LDE factor"
        })
    );
}

#[test]
fn rejects_inconsistent_and_malformed_schedules_without_panicking() {
    for case in 0..9 {
        let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
        match case {
            0 => cfg.whir_schedule.internal_rounds.clear(),
            1 => cfg.whir_schedule.cap_size = 8,
            2 => cfg.whir_schedule.base_round.num_queries = 0,
            3 => cfg.whir_schedule.internal_rounds[0].num_queries = 0,
            4 => cfg.whir_schedule.internal_rounds[0].num_ood_samples = 0,
            5 => cfg.whir_schedule.internal_rounds[0].folding_log2 = 0,
            6 => cfg.whir_schedule.internal_rounds[0].folding_log2 = 12,
            7 => cfg.whir_schedule.internal_rounds[0].folding_log2 = usize::MAX,
            _ => cfg.trace_len_log2 = 7,
        }
        assert!(geometry(&cfg, [1, 1, 1]).is_err(), "case {case}");
        assert!(
            std::panic::catch_unwind(
                || cfg.validate_for_whir_message_size(cfg.whir_message_size_log2())
            )
            .is_err(),
            "CPU validator case {case}"
        );
    }
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.whir_schedule.base_round.fold_log2 = 0;
    assert!(geometry(&cfg, [1, 1, 1]).is_ok());
    cfg.validate_for_whir_message_size(16);
}

#[test]
fn rejects_leaves_larger_than_cosets_and_caps_larger_than_trees() {
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.whir_schedule.base_round.fold_log2 = 17;
    assert_eq!(
        geometry(&cfg, [1, 1, 1]),
        Err(CommitmentGeometryError::LeafExceedsMessage)
    );
    let mut cfg = config(0, CommitmentMode::SeparateMemoryAndWitness);
    cfg.cap_size = 1 << 14;
    cfg.whir_schedule.cap_size = cfg.cap_size;
    assert_eq!(
        geometry(&cfg, [1, 1, 1]),
        Err(CommitmentGeometryError::CapExceedsTree)
    );
    cfg.cap_size = 1024;
    cfg.whir_schedule.cap_size = cfg.cap_size;
    assert_eq!(
        geometry(&cfg, [1, 1, 1]),
        Err(CommitmentGeometryError::CapExceedsTree)
    );
}

#[test]
fn construction_preserves_config_serialization() {
    for pack in 0..=4 {
        let cfg = config(pack, CommitmentMode::SeparateMemoryAndWitness);
        let before = bincode::serialize(&cfg).unwrap();
        geometry(&cfg, [225, 538, 6]).unwrap();
        assert_eq!(bincode::serialize(&cfg).unwrap(), before);
    }
}
