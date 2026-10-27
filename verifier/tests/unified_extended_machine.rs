//! The generated Rust verifier of the unified extended machine
//! (`cs::gkr_circuits::unified_extended_machine`, off the `gkr_circuits!` registry) on the
//! proof fixture `prover/src/tests/gkr/unified_extended_circuit.rs` writes.
mod common;

use common::{SecurityLevel, SoundnessMode};
use verifier_common::errors::DebugErrorCreator;
use verifier_common::test_circuits::CircuitData;

fn circuit() -> CircuitData {
    CircuitData::unregistered(
        "unified_extended_machine",
        "../circuit_defs/unrolled_circuits/unified_extended_machine",
    )
}

#[test]
fn unified_extended_machine_pessimistic_conjecture() {
    let circuit = circuit();
    let (nds, external_challenges) = circuit.load_nds_for_mode(
        SecurityLevel::Sec100,
        SoundnessMode::PessimisticConjecture,
        verifier_common::BLAKE_MODE,
    );
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("gkr verifier unified_extended_machine".to_string())
            .stack_size(common::VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                verifier::unified_extended_machine::pessimistic_conjecture::verify::<
                    _,
                    DebugErrorCreator,
                >(&external_challenges, &mut it)
                .unwrap_or_else(|e| panic!("unified_extended_machine failed: {:?}", e));
            })
            .expect("failed to spawn verifier thread");
        match handle.join() {
            Ok(()) => println!("unified_extended_machine: verification passed"),
            Err(e) => std::panic::resume_unwind(e),
        }
    });
}
