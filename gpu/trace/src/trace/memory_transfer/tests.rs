use super::*;
use prover::definitions::SecurityLevel;
use prover::gkr::prover_config::{BaseColumns, ProverConfig, WhirSchedule};

fn geometry(pack: usize, virtual_packing: bool, memory: usize) -> BaseCommitmentGeometry {
    let mut config = ProverConfig::whir_only(
        20 - pack,
        WhirSchedule::from_legacy_arrays(2, 16, pack, &[1, 5], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    );
    if virtual_packing {
        config.whir_schedule.base_round.fold_log2 = 0;
    }
    BaseCommitmentGeometry::from_config(
        &config,
        BaseColumns {
            memory,
            witness: 5,
            setup: 1,
        },
    )
    .unwrap()
}

#[test]
fn cpu_memory_cap_metadata_rejects_shape_mismatch_before_device_transfer() {
    let caps: Vec<_> = (0..2)
        .map(|_| MerkleTreeCapVarLength {
            cap: vec![[0; 8]; 8],
        })
        .collect();
    let producing = geometry(2, false, 3);
    let host = GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(&caps, producing);
    assert_eq!(host.base_commitment_geometry(), Some(producing));
    host.validate_for_geometry(&producing);
    for wrong in [
        geometry(0, false, 3),
        geometry(2, true, 3),
        geometry(2, false, 4),
    ] {
        assert!(std::panic::catch_unwind(|| host.validate_for_geometry(&wrong)).is_err());
    }
    let legacy = GpuGKRMemoryTransferHost::from_per_coset_caps(&caps, 1, 4);
    legacy.validate_for_geometry(&geometry(0, false, 3));
    assert!(std::panic::catch_unwind(|| legacy.validate_for_geometry(&producing)).is_err());
}

#[test]
fn cpu_virtual_memory_cap_origin_includes_fold_at_k0_and_k2() {
    let caps = vec![
        MerkleTreeCapVarLength {
            cap: vec![[0; 8]; 8]
        };
        2
    ];
    for k in [0, 2] {
        let producing = geometry(k, true, 3);
        let host = GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(&caps, producing);
        assert_eq!(host.base_commitment_geometry(), Some(producing));
        host.validate_for_geometry(&producing);
        let wrong_fold = geometry(k, false, 3);
        assert!(std::panic::catch_unwind(|| host.validate_for_geometry(&wrong_fold)).is_err());
        let legacy = GpuGKRMemoryTransferHost::from_per_coset_caps(&caps, 1, 4);
        assert!(std::panic::catch_unwind(|| legacy.validate_for_geometry(&producing)).is_err());
    }
}

#[test]
fn cpu_empty_memory_caps_and_malformed_metadata_are_checked() {
    let empty = vec![MerkleTreeCapVarLength { cap: Vec::new() }; 2];
    let producing = geometry(2, false, 0);
    let host = GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(&empty, producing);
    assert!(host.unified_tree_cap.is_empty());
    host.validate_for_geometry(&producing);
    assert!(
        std::panic::catch_unwind(|| GpuGKRMemoryTransferHost::from_per_coset_caps(
            &empty,
            u32::MAX,
            4
        ))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(|| GpuGKRMemoryTransferHost::from_per_coset_caps(&empty, 5, 4))
            .is_err()
    );
    assert!(
        std::panic::catch_unwind(|| GpuGKRMemoryTransferHost::from_per_coset_caps(&empty, 1, 4))
            .is_err()
    );
}

#[test]
fn cpu_memory_cap_mode_identity_rejects_before_transfer() {
    use crate::upstream::CommitmentMode;
    let config = ProverConfig::whir_only(
        20,
        WhirSchedule::from_legacy_arrays(2, 16, 0, &[1, 5], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    );
    let columns = BaseColumns {
        memory: 3,
        witness: 5,
        setup: 1,
    };
    let separate = BaseCommitmentGeometry::from_config(&config, columns).unwrap();
    let mut merged_config = config;
    merged_config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let merged = BaseCommitmentGeometry::from_config(&merged_config, columns).unwrap();
    let caps = vec![
        MerkleTreeCapVarLength {
            cap: vec![[0; 8]; 8]
        };
        2
    ];
    let separate_host = GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(&caps, separate);
    let merged_host = GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(&caps, merged);
    let legacy = GpuGKRMemoryTransferHost::from_per_coset_caps(&caps, 1, 4);
    separate_host.validate_for_geometry(&separate);
    merged_host.validate_for_geometry(&merged);
    legacy.validate_for_geometry(&separate);
    for (name, host, requested) in [
        ("merged cap for separate request", &merged_host, separate),
        ("separate cap for merged request", &separate_host, merged),
        ("legacy cap for merged request", &legacy, merged),
    ] {
        let constructed = std::cell::Cell::new(false);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                host.validate_for_geometry(&requested);
                constructed.set(true);
            }))
            .is_err(),
            "{name}"
        );
        assert!(!constructed.get(), "{name} reached transfer construction");
    }
}
