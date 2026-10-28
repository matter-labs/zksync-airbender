use super::*;
use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, BaseColumns, BaseCommitmentGeometry,
};
use gpu_trace::witness::circuit_type::{
    DelegationCircuitType as Delegation, UnrolledCircuitType as Unrolled,
    UnrolledMemoryCircuitType as Memory, UnrolledNonMemoryCircuitType as NonMemory,
};
use prover::gkr::prover_config::{example_configs, CommitmentMode};

const CIRCUITS: [(CircuitType, &str); 15] = [
    (
        CircuitType::Delegation(Delegation::BigIntWithControl),
        "bigint_with_extended_control",
    ),
    (
        CircuitType::Delegation(Delegation::Blake2GFunction),
        "blake2_g_function",
    ),
    (
        CircuitType::Delegation(Delegation::Blake2WithCompression),
        "blake2_with_extended_control",
    ),
    (
        CircuitType::Delegation(Delegation::KeccakSpecial5),
        "keccak_special5",
    ),
    (
        CircuitType::Delegation(Delegation::KeccakColumnParity),
        "keccak_column_parity",
    ),
    (
        CircuitType::Delegation(Delegation::KeccakThetaRho),
        "keccak_theta_rho",
    ),
    (
        CircuitType::Delegation(Delegation::KeccakChi5),
        "keccak_chi5",
    ),
    (
        CircuitType::Unrolled(Unrolled::InitsAndTeardowns),
        "inits_and_teardowns",
    ),
    (
        CircuitType::Unrolled(Unrolled::Unified),
        "unified_reduced_machine",
    ),
    (
        CircuitType::Unrolled(Unrolled::Memory(Memory::LoadStoreSubwordOnly)),
        "mem_subword_only",
    ),
    (
        CircuitType::Unrolled(Unrolled::Memory(Memory::LoadStoreWordOnly)),
        "mem_word_only",
    ),
    (
        CircuitType::Unrolled(Unrolled::NonMemory(NonMemory::AddSubLuiAuipcMop)),
        "add_sub_lui_auipc_mop",
    ),
    (
        CircuitType::Unrolled(Unrolled::NonMemory(NonMemory::JumpBranchSlt)),
        "jump_branch_slt",
    ),
    (
        CircuitType::Unrolled(Unrolled::NonMemory(NonMemory::MulDivUnsigned)),
        "unsigned_mul_div",
    ),
    (
        CircuitType::Unrolled(Unrolled::NonMemory(NonMemory::ShiftBinary)),
        "shift_binop",
    ),
];

fn artifact(name: &str) -> GKRCircuitArtifact<BF> {
    let path = format!(
        "{}/../../cs/compiled_circuits/{name}_layout_gkr.json",
        env!("CARGO_MANIFEST_DIR")
    );
    serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap()
}

#[test]
fn cpu_builds_prover_config_for_all_supported_security_levels() {
    let mut checked = 0;
    let mut virtual_defaults = 0;
    for (circuit, name) in CIRCUITS {
        let compiled = artifact(name);
        let columns = BaseColumns::of(&compiled);
        for level in GPU_SUPPORTED_SECURITY_LEVELS {
            let cfg = prover_config(circuit, level).unwrap();
            assert_eq!(cfg, circuit.prover_config(level));
            assert_eq!(cfg.security_level, level);
            assert!(
                cfg.cap_size >= cfg.lde_factor(),
                "canonical memory cap must cover every LDE coset: {circuit:?}"
            );
            assert_eq!(cfg.trace_len_log2, circuit.get_domain_size_log2() as usize);
            assert_eq!(compiled.trace_len, 1 << cfg.trace_len_log2);
            cfg.validate_for_whir_message_size(cfg.whir_message_size_log2());
            let shape = BaseCommitmentGeometry::from_config(&cfg, columns)
                .unwrap_or_else(|error| panic!("{circuit:?}/{level:?}: {error}"));
            assert_eq!(shape.logical_columns(), columns);
            assert_eq!(shape.is_virtual_packing(), cfg.is_virtual_packing());
            assert_eq!(
                shape.total_physical_columns(),
                columns.committed_polys(cfg.pack_log2(), cfg.merged_memory_and_witness())
            );
            if matches!(circuit, CircuitType::Delegation(_)) {
                assert!(shape.is_virtual_packing());
                virtual_defaults += 1;
            } else {
                assert_eq!(shape.pack_log2(), 0);
                assert!(!shape.is_virtual_packing());
                gpu_trace::trace::memory::assert_unpacked_prover_config(&cfg);
            }
            checked += 1;
        }
    }
    assert_eq!(checked, 15 * GPU_SUPPORTED_SECURITY_LEVELS.len());
    assert_eq!(virtual_defaults, 7 * GPU_SUPPORTED_SECURITY_LEVELS.len());
}

#[test]
fn unified_uses_its_canonical_schedule() {
    let circuit = CircuitType::Unrolled(Unrolled::Unified);
    for &level in GPU_SUPPORTED_SECURITY_LEVELS.iter() {
        let actual = prover_config(circuit, level).unwrap();
        let expected = config_for_security_level_under_pessimistic_conjecture(23, level);
        assert_eq!(actual.whir_schedule, expected.whir_schedule);
    }
}

#[test]
fn cpu_virtual_defaults_remain_rejected_by_existing_gpu_guard() {
    let mut rejected = 0;
    for (circuit, name) in CIRCUITS {
        if !matches!(circuit, CircuitType::Delegation(_)) {
            continue;
        }
        for level in GPU_SUPPORTED_SECURITY_LEVELS {
            let cfg = prover_config(circuit, level).unwrap();
            let panic = std::panic::catch_unwind(|| {
                gpu_trace::trace::memory::assert_unpacked_prover_config(&cfg)
            })
            .expect_err("packed or virtual default must still fail closed");
            let text = panic
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic.downcast_ref::<&str>().copied())
                .unwrap();
            let expected = if cfg.pack_log2() > 0 {
                "base-commitment packing"
            } else {
                "virtual packing"
            };
            assert!(text.contains(expected), "{circuit:?}: {text}");
            eprintln!(
                "baseline rejection {name}: {expected} (k={}, f={})",
                cfg.pack_log2(),
                cfg.base_round().fold_log2
            );
            rejected += 1;
        }
    }
    assert_eq!(rejected, 7 * GPU_SUPPORTED_SECURITY_LEVELS.len());
}

#[test]
fn cpu_batching_pow_keeps_base_round_override_and_physical_count() {
    let compiled = artifact("blake2_with_extended_control");
    for (trace, pack) in [(20, 0), (20, 2), (20, 4)] {
        let mut cfg =
            example_configs::packed_config_for_security_level_under_pessimistic_conjecture(
                trace,
                pack,
                SecurityLevel::Sec100,
            );
        let shape = BaseCommitmentGeometry::from_config(&cfg, BaseColumns::of(&compiled)).unwrap();
        assert_eq!(
            cfg.commitment_mode,
            CommitmentMode::SeparateMemoryAndWitness
        );
        let expected = cfg.base_round().batching_pow_bits::<BF, E4>(
            cfg.security_level.security_bits(),
            shape.message_size_log2(),
            shape.total_physical_columns(),
        );
        assert_eq!(batched_proximity_check_pow_bits(&cfg, &compiled), expected);
        cfg.whir_schedule.base_round.batching_pow_bits = Some(7);
        assert_eq!(batched_proximity_check_pow_bits(&cfg, &compiled), 7);
    }
}
