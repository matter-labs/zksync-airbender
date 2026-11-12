//! Every canonical circuit proof in both modes, preverified and embedded outside Miri.
#[path = "common/miri_circuit_stream.rs"]
mod miri_circuit_stream;

macro_rules! tests {
    ($($name:ident; $path:expr),* $(,)?) => {
        paste::paste! {
            $(
                #[test]
                fn [<$name _pessimistic_conjecture>]() {
                    check(stringify!($name), 0, include_bytes!(concat!(
                        env!("AIRBENDER_MIRI_CIRCUIT_INPUT_DIR"), "/pessimistic_conjecture/", stringify!($name), ".bin"
                    )));
                }
                #[test]
                fn [<$name _ethproofs_soundcalc>]() {
                    check(stringify!($name), 1, include_bytes!(concat!(
                        env!("AIRBENDER_MIRI_CIRCUIT_INPUT_DIR"), "/ethproofs_soundcalc/", stringify!($name), ".bin"
                    )));
                }
            )*
        }
    };
}
fn check(name: &str, mode: u32, input: &[u8]) {
    assert_eq!(
        verifier::verifier_common::BLAKE_MODE,
        verifier::verifier_common::BlakeMode::Compression
    );
    miri_circuit_stream::check(name, mode, input);
}
verifier::verifier_common::gkr_fixture_circuits!(tests);
