//! Per-program `Setups` assembly without proving.
//!
//! The provers (`prover_examples::{unrolled,unified}`) build the
//! `Setups` map — one committed setup cap per circuit family — as a
//! by-product of proving. Drivers and verifiers need the same map without
//! running a prover: the setup caps prefix every non-determinism stream the
//! `fsv_*` verifiers consume, and a verifier that wants to bind a proof to a
//! *supplied* program (rather than trusting proof-carried metadata) must
//! recompute the caps from the binary alone. The commitment parameters here
//! must stay in lockstep with what the provers use — same
//! `config_for_security_level_under_pessimistic_conjecture`, LDE factor,
//! WHIR schedule head, and cap size — or the recomputed caps stop
//! byte-matching proof-time setups.

use super::*;
use prover::definitions::SecurityLevel;
use prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture;
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
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
    for (start_offset, window) in binary.windows(riscv_common::EXIT_SEQUENCE.len()).enumerate() {
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

/// `Setups` map for an UNROLLED execution of `(binary, text)` on machine `C`:
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
    let per_family = get_unrolled_circuits_setups_for_machine_type::<C, A>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    commit_setup_params(
        per_family
            .into_iter()
            .map(|(family_idx, setup)| (family_idx as u32, setup.trace_len, setup.setup)),
        security_level,
        worker,
    )
}

/// `Setups` map for a UNIFIED (reduced-machine) execution of `(binary, text)`:
/// the single unified-family entry, committed exactly like the provers do.
/// Inputs must already be padded for proving.
pub fn compute_unified_program_setups<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    security_level: SecurityLevel,
    worker: &Worker,
) -> Setups {
    let unified_setup =
        unified_reduced_machine_circuit_setup::<A>(binary_image, text_section, use_caches, worker);
    commit_setup_params(
        core::iter::once((
            common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            unified_setup.trace_len,
            unified_setup.setup,
        )),
        security_level,
        worker,
    )
}

fn commit_setup_params(
    circuit_setups: impl Iterator<Item = (u32, usize, GKRSetup<BabyBearField>)>,
    security_level: SecurityLevel,
    worker: &Worker,
) -> Setups {
    let mut twiddles: HashMap<usize, Twiddles<BabyBearField, Global>> = HashMap::new();
    let mut result: Setups = BTreeMap::new();
    for (family_idx, trace_len, setup) in circuit_setups {
        let prover_config = config_for_security_level_under_pessimistic_conjecture(
            trace_len.trailing_zeros() as usize,
            security_level,
        );
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let setup_commitment = setup.commit::<DefaultTreeConstructor>(
            &*twiddles_for_size,
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            worker,
        );
        result.insert(
            family_idx,
            UnrolledCircuitSetupParams::from_setup_tree_cap(
                family_idx,
                trace_len as u32,
                <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BabyBearField>>::get_cap(
                    &setup_commitment.tree,
                ),
            ),
        );
    }
    result
}
