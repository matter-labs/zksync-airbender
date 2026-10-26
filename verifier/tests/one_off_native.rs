//! ONE-OFF native run of an experiment verifier (a `generated/<circuit>/<suffix>`
//! module that is not registered in the crate) on an experiment proof. Edit
//! the `#[path]` and the proof suffix, then
//! `cargo test --release --test one_off_native -- --ignored --nocapture`.
#[macro_use]
mod common;

use field::baby_bear::base::BabyBearField;
use verifier_common::errors::DebugErrorCreator;

#[path = "../src/generated/add_sub_lui_auipc_mop/ethproofs_soundcalc_mp/mod.rs"]
#[allow(dead_code, unused_imports)]
mod one_off;

#[test]
#[ignore = "one-off experiment: needs the generated module and the proof named in the source"]
fn one_off_native() {
    let name = "add_sub_lui_auipc_mop";
    let suffix = "sec_100_ethproofs_soundcalc_mp";
    let circuit = common::circuit_by_name(name);
    let proof_path = format!(
        "{}/../prover/test_proofs/{}_{}_gkr_proof.json",
        env!("CARGO_MANIFEST_DIR"),
        name,
        suffix
    );
    let proof: prover::gkr::prover::GKRProof<
        BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    > = serde_json::from_reader(std::io::BufReader::new(
        std::fs::File::open(&proof_path).unwrap_or_else(|e| panic!("{proof_path}: {e}")),
    ))
    .unwrap();
    let compiled = circuit.compiled_circuit();
    let nds = verifier_common::gkr::flatten::flatten_gkr_proof_for_nds::<
        BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    >(&proof, &compiled);
    println!("{name}_{suffix}: oracle data length: {} u32 words", nds.len());
    let external_challenges = proof.external_challenges;
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .stack_size(common::VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                one_off::verify::<_, DebugErrorCreator>(&external_challenges, &mut it)
                    .unwrap_or_else(|e| panic!("{name} {suffix} failed: {e:?}"));
                assert!(it.next().is_none(), "unconsumed non-determinism words");
            })
            .expect("failed to spawn verifier thread");
        handle.join().unwrap();
    });
    println!("{name}_{suffix}: verification passed");
}
