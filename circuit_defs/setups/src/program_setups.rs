//! Per-program `Setups` assembly without proving.
//!
//! The provers (`program_prover::{unrolled,unified}`) build the
//! `Setups` map — one committed setup cap per circuit family — as a
//! by-product of proving. Drivers and verifiers need the same map without
//! running a prover: the setup caps prefix every non-determinism stream the
//! `fsv_*` verifiers consume, and a verifier that wants to bind a proof to a
//! *supplied* program (rather than trusting proof-carried metadata) must
//! recompute the caps from the binary alone. The commitment parameters here
//! must stay in lockstep with the prover's selected compiled-circuit config
//! (or explicit L1 profile override): the same LDE factor, WHIR schedule head
//! and cap size, or the recomputed caps stop
//! byte-matching proof-time setups.

use super::*;
use prover::definitions::{SecurityLevel, SoundnessMode};
use prover::gkr::prover_config::{ProofProfile, ProverConfig};
use prover::merkle_trees::MerkleTreeCapVarLength;
use std::collections::BTreeMap;
use std::collections::HashMap;

pub type SetupCommitter<'a> =
    dyn FnMut(&ProverConfig, &GKRSetup<BabyBearField>) -> MerkleTreeCapVarLength + 'a;

/// CPU setup commitment with twiddles reused across a program's circuit families.
pub fn cpu_setup_committer(
    worker: &Worker,
) -> impl FnMut(&ProverConfig, &GKRSetup<BabyBearField>) -> MerkleTreeCapVarLength + '_ {
    let mut twiddles: HashMap<usize, Twiddles<BabyBearField, Global>> = HashMap::new();
    move |config, setup| {
        let size = 1usize << config.whir_message_size_log2();
        let twiddles = twiddles
            .entry(size)
            .or_insert_with(|| Twiddles::new(size, worker));
        setup
            .commit_for_config::<DefaultTreeConstructor>(&*twiddles, config, worker)
            .get_cap()
    }
}

/// Statically derive a program's exit PC: the address of the final opcode of
/// the unique [`riscv_common::EXIT_SEQUENCE`] occurrence in the binary. This
/// is the `final_pc` a completed execution of the program ends on, and the
/// value hashed into the program's `end_params`.
///
/// Moved from the retired `execution_utils` crate (input is words rather
/// than bytes).
pub fn find_binary_exit_point(binary: &[u32]) -> u32 {
    let mut candidates = vec![];
    for (start_offset, window) in binary
        .windows(riscv_common::EXIT_SEQUENCE.len())
        .enumerate()
    {
        if window == riscv_common::EXIT_SEQUENCE {
            candidates.push(start_offset);
        }
    }
    assert_eq!(
        candidates.len(),
        1,
        "expected exactly one exit-sequence occurrence, found {}",
        candidates.len()
    );
    let final_pc =
        (candidates[0] + riscv_common::EXIT_SEQUENCE.len() - 1) * core::mem::size_of::<u32>();
    final_pc as u32
}

/// Mode-explicit setup reconstruction from each family's actual compiled columns.
pub fn compute_unrolled_program_setups_in_mode<C: MachineConfig, A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    soundness_mode: SoundnessMode,
    worker: &Worker,
    commit: &mut SetupCommitter<'_>,
) -> Setups {
    let per_family = get_unrolled_circuits_setups_for_machine_type::<C, A>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    let configs_and_setups = per_family.into_iter().map(|(family_idx, setup)| {
        let config = setup.prover_config_in_mode(security_level, soundness_mode);
        (family_idx as u32, config, setup.setup)
    });
    commit_setup_params(configs_and_setups, security_level, commit)
}

/// Mode-explicit unified setup reconstruction from actual compiled columns.
pub fn compute_unified_program_setups_in_mode<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    soundness_mode: SoundnessMode,
    worker: &Worker,
    commit: &mut SetupCommitter<'_>,
) -> Setups {
    let unified_setup =
        unified_reduced_machine_circuit_setup::<A>(binary_image, text_section, use_caches, worker);
    let config = unified_setup.prover_config_in_mode(security_level, soundness_mode);
    commit_setup_params(
        core::iter::once((
            common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            config,
            unified_setup.setup,
        )),
        security_level,
        commit,
    )
}

/// Setups of the unified family under an explicit proof profile and soundness mode.
pub fn compute_unified_program_setups_for_profile<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    profile: ProofProfile,
    soundness_mode: SoundnessMode,
    worker: &Worker,
    commit: &mut SetupCommitter<'_>,
) -> Setups {
    let unified_setup = match profile {
        ProofProfile::Compression => unified_reduced_machine_circuit_setup::<A>(
            binary_image,
            text_section,
            use_caches,
            worker,
        ),
        ProofProfile::CompressionFinal => unified_reduced_machine_2_22_circuit_setup::<A>(
            binary_image,
            text_section,
            use_caches,
            worker,
        ),
        _ => panic!("special unified setups require a compression profile"),
    };
    let config = profile.prover_config(unified_setup.trace_len.ilog2() as usize, soundness_mode);
    assert_eq!(
        unified_setup.trace_len.ilog2() as usize,
        config.trace_len_log2
    );
    commit_setup_params(
        core::iter::once((
            common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            config,
            unified_setup.setup,
        )),
        security_level,
        commit,
    )
}

/// Commit every setup with ITS circuit's prover config (the geometry the
/// provers use), keyed by circuit family.
fn commit_setup_params(
    circuit_setups: impl Iterator<Item = (u32, ProverConfig, GKRSetup<BabyBearField>)>,
    security_level: SecurityLevel,
    commit: &mut SetupCommitter<'_>,
) -> Setups {
    let mut result: Setups = BTreeMap::new();
    for (family_idx, prover_config, setup) in circuit_setups {
        assert_eq!(prover_config.security_level, security_level);
        let trace_len = 1usize << prover_config.trace_len_log2;
        let setup_cap = commit(&prover_config, &setup);
        result.insert(
            family_idx,
            UnrolledCircuitSetupParams::from_setup_tree_cap(
                family_idx,
                trace_len as u32,
                setup_cap,
                prover_config.cap_size,
            ),
        );
    }
    result
}
