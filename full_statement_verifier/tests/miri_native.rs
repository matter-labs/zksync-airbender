//! Pessimistic statements with recorded inner verifier outputs over static inputs.
#[path = "common/miri_stream.rs"]
mod miri_stream;

use full_statement_verifier::verifier_common::{self, BlakeMode};

fn check(input: &[u8], selection: miri_stream::Selection) {
    assert_eq!(verifier_common::BLAKE_MODE, BlakeMode::Compression);
    let (expected, mut nds) = miri_stream::decode(input);
    let output = selection.verify_mocked(&mut nds);
    assert_eq!(output, expected);
}

macro_rules! statement_test {
    ($name:ident, $file:literal, $entry:expr) => {
        #[test]
        fn $name() {
            const INPUT: &[u8] = include_bytes!(concat!(
                env!(
                    "AIRBENDER_MIRI_FSV_INPUT_DIR",
                    "prepare B.bin, R.bin and D.bin with the miri_input example"
                ),
                "/",
                $file
            ));
            check(INPUT, $entry);
        }
    };
}

statement_test!(
    unrolled_base_layer,
    "B.bin",
    miri_stream::Selection::UnrolledBase
);
statement_test!(
    unrolled_recursion_layer,
    "R.bin",
    miri_stream::Selection::UnrolledRecursion
);
statement_test!(
    unified_recursion_dispatch,
    "D.bin",
    miri_stream::Selection::RecursionDispatch
);
