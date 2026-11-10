#[test]
fn repository_and_output_roots_are_independent() {
    let temporary =
        std::env::temp_dir().join(format!("proof-fixtures-roots-{}", std::process::id()));
    let repository = temporary.join("repository");
    let output = temporary.join("output");
    std::env::set_var("AB_TEST_ARTIFACT_ROOT", &repository);
    std::env::set_var("PROOF_FIXTURES_OUTPUT_ROOT", &output);
    assert_eq!(proof_fixtures::root(), repository);
    assert_eq!(proof_fixtures::output_root(), output);
    assert_eq!(
        proof_fixtures::circuit_proof("pessimistic_conjecture", "shift_binop"),
        repository.join("fixtures/circuits/pessimistic_conjecture/shift_binop.json.zlib")
    );
    assert_eq!(
        proof_fixtures::chain_artifact("ethproofs_soundcalc", "unrolled"),
        repository.join("fixtures/chains/ethproofs_soundcalc/unrolled.json.zlib")
    );
    std::env::remove_var("PROOF_FIXTURES_OUTPUT_ROOT");
    assert_eq!(proof_fixtures::output_root(), repository);
}
