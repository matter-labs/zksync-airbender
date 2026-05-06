use prover::definitions::GKRExternalChallenges;
pub use verifier_common::test_circuits::{CircuitData, CIRCUITS};

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::errors::{DebugErrorCreator, VerificationError};
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

pub const VERIFIER_STACK_SIZE: usize = 1 << 27;

macro_rules! define_dispatch {
    ($($name:ident: $schedule_80:ident: $schedule_100:ident: $layout_suffix:expr),* $(,)?) => {
        macro_rules! with_circuit {
            ($circuit_name:expr, $level:expr, |$m:ident| $body:expr) => {
                match ($circuit_name, $level) {
                    $(
                        #[cfg(feature = "security_80")]
                        (stringify!($name), $crate::common::SecurityLevel::Sec80) => {
                            use verifier::$name::sec_80 as $m;
                            $body
                        }
                        #[cfg(feature = "security_100")]
                        (stringify!($name), $crate::common::SecurityLevel::Sec100) => {
                            use verifier::$name::sec_100 as $m;
                            $body
                        }
                    )*
                    (other, _) => panic!("unknown or disabled circuit/level: {}", other),
                }
            };
        }
    };
}
verifier_common::gkr_circuits!(define_dispatch);

pub use verifier_common::test_circuits::SecurityLevel;

pub fn load_nds(
    name: &str,
    level: SecurityLevel,
) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
    circuit_by_name(name).load_nds_for(level)
}

pub fn binary_paths(name: &str, level: SecurityLevel) -> (String, String, String) {
    circuit_by_name(name).binary_paths_for(level)
}

pub fn circuit_by_name(name: &str) -> &'static CircuitData {
    CIRCUITS
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("unknown circuit: {}", name))
}

#[derive(Debug)]
pub enum VerifyRejection {
    Error(VerificationError),
    Panic(String),
}

pub fn verify_nds(
    name: &str,
    level: SecurityLevel,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    nds: Vec<u32>,
) -> Result<(), VerifyRejection> {
    let prev_hook = std::panic::take_hook();
    let panic_msg = std::sync::Arc::new(std::sync::Mutex::new(None::<String>));
    let panic_msg_clone = panic_msg.clone();
    std::panic::set_hook(Box::new(move |info| {
        *panic_msg_clone.lock().unwrap() = Some(format!("{}", info));
    }));

    let outcome: Result<Result<(), VerificationError>, ()> = std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("verify_{}_{:?}", name, level))
            .stack_size(VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, level, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>(external_challenges)
                        .map(|_| ())
                })
            })
            .expect("failed to spawn thread");

        handle.join().map_err(|_| ())
    });

    std::panic::set_hook(prev_hook);

    match outcome {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(VerifyRejection::Error(e)),
        Err(()) => {
            let msg = panic_msg
                .lock()
                .unwrap()
                .take()
                .unwrap_or_else(|| "(no panic message captured)".to_string());
            Err(VerifyRejection::Panic(msg))
        }
    }
}

pub fn assert_rejects_corrupted_nds(
    name: &str,
    level: SecurityLevel,
    label: &str,
    corrupt: impl FnOnce(&mut Vec<u32>),
    expected: impl FnOnce(&VerifyRejection) -> bool,
) {
    let (mut nds, external_challenges) = load_nds(name, level);
    corrupt(&mut nds);
    match verify_nds(name, level, &external_challenges, nds) {
        Ok(()) => panic!("{}: should reject {}", name, label),
        Err(r) => assert!(
            expected(&r),
            "{}: {} rejected with unexpected rejection: {:?}",
            name,
            label,
            r
        ),
    }
}

pub fn proof_to_nds(
    name: &str,
    level: SecurityLevel,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
    let circuit_data = circuit_by_name(name);
    let compiled = circuit_data.compiled_circuit();
    let inits_and_teardowns_top_bits: Vec<u32> = (0..compiled.memory_layout.teardown_sets.len())
        .map(|i| i as u32)
        .collect();
    let nds = flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        proof,
        &compiled,
        circuit_data.whir_schedule_for(level),
        &inits_and_teardowns_top_bits,
    );
    let external_challenges = proof.external_challenges;

    (nds, external_challenges)
}

pub fn assert_rejects_with_variant(
    name: &str,
    level: SecurityLevel,
    label: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
    expected: impl FnOnce(&VerificationError) -> bool,
) {
    let (nds, external_challenges) = proof_to_nds(name, level, proof);
    match verify_nds(name, level, &external_challenges, nds) {
        Ok(()) => panic!("{}: should reject {}", name, label),
        Err(VerifyRejection::Error(e)) => {
            assert!(
                expected(&e),
                "{}: {} rejected with unexpected variant {:?}",
                name,
                label,
                e
            );
        }
        Err(VerifyRejection::Panic(msg)) => {
            panic!(
                "{}: {} rejected via panic (expected specific error variant): {}",
                name, label, msg
            );
        }
    }
}

pub fn assert_rejects_via_panic(
    name: &str,
    level: SecurityLevel,
    label: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) {
    let (nds, external_challenges) = proof_to_nds(name, level, proof);
    match verify_nds(name, level, &external_challenges, nds) {
        Ok(()) => panic!("{}: should reject {}", name, label),
        Err(VerifyRejection::Panic(_)) => {}
        Err(VerifyRejection::Error(e)) => {
            panic!(
                "{}: {} rejected via error {:?} (expected panic)",
                name, label, e
            );
        }
    }
}

pub fn load_binary_section(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|_| {
        panic!(
            "Missing {} — run `cd tools/gkr_verifier && ./dump_bin.sh` first",
            path
        )
    });
    assert!(bytes.len() % 4 == 0);
    bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}
