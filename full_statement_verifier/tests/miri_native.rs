//! Every committed chain in both soundness modes with recorded inner verifier outputs.
//! The Pessimistic compression step has no committed input and is outside Miri coverage.
#[path = "common/miri_stream.rs"]
mod miri_stream;

use full_statement_verifier::verifier_common::{
    self, prover::definitions::SoundnessMode, BlakeMode,
};
use miri_stream::{Chain, Selection};

fn check(input: &[u8], selection: miri_stream::Selection) {
    assert_eq!(verifier_common::BLAKE_MODE, BlakeMode::Compression);
    let (expected, mut nds) = miri_stream::decode(input);
    let output = selection.verify_mocked(&mut nds);
    assert_eq!(output, expected);
}

macro_rules! statement_test {
    ($name:ident, $mode:ident, $chain:ident) => {
        #[test]
        fn $name() {
            const INPUT: &[u8] = include_bytes!(concat!(
                env!(
                    "AIRBENDER_MIRI_FSV_INPUT_DIR",
                    "prepare <mode>_<chain>.bin with the miri_input example"
                ),
                "/",
                stringify!($name),
                ".bin"
            ));
            check(
                INPUT,
                Selection {
                    mode: SoundnessMode::$mode,
                    chain: Chain::$chain,
                },
            );
        }
    };
}

statement_test!(pessimistic_conjecture_base, PessimisticConjecture, Base);
statement_test!(
    pessimistic_conjecture_unrolled,
    PessimisticConjecture,
    Unrolled
);
statement_test!(
    pessimistic_conjecture_unified,
    PessimisticConjecture,
    Unified
);
statement_test!(
    pessimistic_conjecture_unrolled_unified,
    PessimisticConjecture,
    UnrolledUnified
);
statement_test!(
    pessimistic_conjecture_compression,
    PessimisticConjecture,
    Compression
);
statement_test!(ethproofs_soundcalc_base, EthproofsSoundnessCalc, Base);
statement_test!(
    ethproofs_soundcalc_unrolled,
    EthproofsSoundnessCalc,
    Unrolled
);
statement_test!(ethproofs_soundcalc_unified, EthproofsSoundnessCalc, Unified);
statement_test!(
    ethproofs_soundcalc_unrolled_unified,
    EthproofsSoundnessCalc,
    UnrolledUnified
);
statement_test!(
    ethproofs_soundcalc_compression,
    EthproofsSoundnessCalc,
    Compression
);
