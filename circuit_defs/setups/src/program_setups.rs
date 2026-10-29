//! Per-program `Setups` assembly without proving.
//!
//! The provers (`prover_examples::{unrolled,unified}`) build the
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
use prover::gkr::prover_config::example_configs::ConfigSelectionError;
use prover::gkr::prover_config::{ProofProfile, ProverConfig};
use std::collections::BTreeMap;
use std::collections::HashMap;

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

/// Pessimistic compatibility wrapper: `Setups` for an UNROLLED execution of `(binary, text)` on machine `C`:
/// one entry per circuit family of the machine, with the setup cap committed
/// exactly like the provers do. Inputs must already be padded for proving
/// (`pad_bytecode_for_proving` / `read_and_pad_binary`).
pub fn compute_unrolled_program_setups<C: MachineConfig, A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    worker: &Worker,
) -> Setups {
    compute_unrolled_program_setups_in_mode::<C, A>(
        binary_image,
        text_section,
        use_caches,
        security_level,
        SoundnessMode::PessimisticConjecture,
        worker,
    )
    .unwrap_or_else(|error| panic!("{error}"))
}

/// Mode-explicit setup reconstruction from each family's actual compiled columns.
pub fn compute_unrolled_program_setups_in_mode<C: MachineConfig, A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    soundness_mode: SoundnessMode,
    worker: &Worker,
) -> Result<Setups, ConfigSelectionError> {
    let per_family = get_unrolled_circuits_setups_for_machine_type::<C, A>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    let configs_and_setups = per_family
        .into_iter()
        .map(|(family_idx, setup)| {
            let config = setup.try_prover_config_in_mode(security_level, soundness_mode)?;
            Ok((family_idx as u32, config, setup.setup))
        })
        .collect::<Result<Vec<_>, ConfigSelectionError>>()?;
    Ok(commit_setup_params(
        configs_and_setups.into_iter(),
        security_level,
        worker,
    ))
}

/// Pessimistic compatibility wrapper: `Setups` for a UNIFIED (reduced-machine) execution of `(binary, text)`:
/// the single unified-family entry, committed exactly like the provers do.
/// Inputs must already be padded for proving.
pub fn compute_unified_program_setups<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    worker: &Worker,
) -> Setups {
    compute_unified_program_setups_in_mode::<A>(
        binary_image,
        text_section,
        use_caches,
        security_level,
        SoundnessMode::PessimisticConjecture,
        worker,
    )
    .unwrap_or_else(|error| panic!("{error}"))
}

/// Mode-explicit unified setup reconstruction from actual compiled columns.
pub fn compute_unified_program_setups_in_mode<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    soundness_mode: SoundnessMode,
    worker: &Worker,
) -> Result<Setups, ConfigSelectionError> {
    let unified_setup =
        unified_reduced_machine_circuit_setup::<A>(binary_image, text_section, use_caches, worker);
    let config = unified_setup.try_prover_config_in_mode(security_level, soundness_mode)?;
    Ok(commit_setup_params(
        core::iter::once((
            common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            config,
            unified_setup.setup,
        )),
        security_level,
        worker,
    ))
}

/// Pessimistic setups of the unified family under an explicit proof profile.
pub fn compute_unified_program_setups_for_profile<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    profile: ProofProfile,
    worker: &Worker,
) -> Setups {
    let unified_setup = match profile {
        ProofProfile::Standard | ProofProfile::L1FeederA => {
            unified_reduced_machine_circuit_setup::<A>(
                binary_image,
                text_section,
                use_caches,
                worker,
            )
        }
        ProofProfile::L1Feeder => unified_reduced_machine_2_22_circuit_setup::<A>(
            binary_image,
            text_section,
            use_caches,
            worker,
        ),
        ProofProfile::L1Wrap => {
            panic!("ProofProfile::L1Wrap setups are built by unified_reduced_machine_proth120")
        }
    };
    let config = setup_prover_config(profile, unified_setup.prover_config(security_level));
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
        worker,
    )
}

fn setup_prover_config(profile: ProofProfile, circuit_config: &ProverConfig) -> ProverConfig {
    match profile {
        ProofProfile::Standard => circuit_config.clone(),
        ProofProfile::L1Feeder | ProofProfile::L1FeederA => {
            profile.prover_config(circuit_config.trace_len_log2, circuit_config.security_level)
        }
        ProofProfile::L1Wrap => panic!("L1Wrap setups use the Proth120 circuit"),
    }
}

/// Commit every setup with ITS circuit's prover config (the geometry the
/// provers use), keyed by circuit family.
fn commit_setup_params(
    circuit_setups: impl Iterator<Item = (u32, ProverConfig, GKRSetup<BabyBearField>)>,
    security_level: SecurityLevel,
    worker: &Worker,
) -> Setups {
    let mut twiddles: HashMap<usize, Twiddles<BabyBearField, Global>> = HashMap::new();
    let mut result: Setups = BTreeMap::new();
    for (family_idx, prover_config, setup) in circuit_setups {
        assert_eq!(prover_config.security_level, security_level);
        let trace_len = 1usize << prover_config.trace_len_log2;
        let twiddles_size = 1usize << prover_config.whir_message_size_log2();
        let twiddles_for_size = twiddles
            .entry(twiddles_size)
            .or_insert_with(|| Twiddles::new(twiddles_size, worker));
        let setup_commitment = setup.commit_for_config::<DefaultTreeConstructor>(
            &*twiddles_for_size,
            &prover_config,
            worker,
        );
        result.insert(
            family_idx,
            UnrolledCircuitSetupParams::from_setup_tree_cap(
                family_idx,
                trace_len as u32,
                setup_commitment.get_cap(),
                prover_config.cap_size,
            ),
        );
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_common::RiscVCycleCircuit;

    #[test]
    fn standard_setup_keeps_the_circuit_config() {
        for &level in SecurityLevel::ALL {
            for config in [
                <unified_reduced_machine::UnifiedReducedMachineCircuit as RiscVCycleCircuit<BabyBearField, true>>::prover_config(level),
                <unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<BabyBearField, true>>::prover_config(level),
            ] {
                assert_eq!(setup_prover_config(ProofProfile::Standard, &config), config);
            }
        }
    }

    #[test]
    fn feeder_setup_overrides_the_circuit_default() {
        for (profile, expected, standard) in [
            (
                ProofProfile::L1Feeder,
                prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_22(),
                <unified_reduced_machine_2_22::UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<BabyBearField, true>>::prover_config(SecurityLevel::Sec100),
            ),
            (
                ProofProfile::L1FeederA,
                prover::gkr::prover_config::example_configs::l1_feeder_a_config_for_2_23(),
                <unified_reduced_machine::UnifiedReducedMachineCircuit as RiscVCycleCircuit<BabyBearField, true>>::prover_config(SecurityLevel::Sec100),
            ),
        ] {
            assert_ne!(standard, expected);
            assert_eq!(setup_prover_config(profile, &standard), expected);
        }
    }
}
