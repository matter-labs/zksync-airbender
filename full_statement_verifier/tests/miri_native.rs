//! Full production-encoding verifier over natively prepared static input.
#[path = "common/miri_stream.rs"]
mod miri_stream;

use full_statement_verifier::verifier_common::{self, errors::DebugErrorCreator, BlakeMode};

// Missing input must fail compilation. No filesystem access is interpreted.
const INPUT: &[u8] = include_bytes!(env!(
    "AIRBENDER_MIRI_FSV_INPUT",
    "generate static input with full_statement_verifier's miri_input example"
));

#[test]
fn hashed_fibonacci_unrolled_base_layer() {
    assert_eq!(verifier_common::BLAKE_MODE, BlakeMode::Compression);
    let (expected, mut nds) = miri_stream::decode(INPUT);
    let output = full_statement_verifier::pessimistic_conjecture::verify_unrolled_base_layer::<
        _,
        DebugErrorCreator,
        { verifier_common::USE_REDUCED_BLAKE2_ROUNDS },
    >(&mut nds)
    .unwrap();
    std::hint::black_box(output);
    assert_eq!(output, expected);
    assert!(
        nds.next().is_none(),
        "full statement verifier left NDS words"
    );
}
