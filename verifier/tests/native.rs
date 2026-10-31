#[macro_use]
mod common;

use common::{SecurityLevel, SoundnessMode};
use verifier_common::errors::DebugErrorCreator;

fn run_native(name: &str, level: SecurityLevel, mode: SoundnessMode) {
    let (nds, external_challenges) =
        common::load_nds_in_mode(name, level, mode, verifier_common::BLAKE_MODE);
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("gkr verifier {} {:?}", name, level))
            .stack_size(common::VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                // set_iterator(nds.into_iter());
                with_circuit!(name, level, mode, |m| {
                    m::verify::<_, DebugErrorCreator>(&external_challenges, &mut it)
                        .unwrap_or_else(|e| {
                            panic!("{} {:?} {:?} failed: {:?}", name, level, mode, e)
                        });
                });
                #[cfg(feature = "verifier_stats")]
                common::print_stats_log(name);
            })
            .expect("failed to spawn verifier thread");

        match handle.join() {
            Ok(()) => println!("{} {:?} {:?}: verification passed", name, level, mode),
            Err(e) => std::panic::resume_unwind(e),
        }
    });
}

macro_rules! generate_native_tests {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        paste::paste! {
            $(
                #[test]
                fn [<$name _pessimistic_conjecture>]() {
                    run_native(stringify!($name), SecurityLevel::Sec100, SoundnessMode::PessimisticConjecture);
                }
                /// The `<circuit>_sec_100_ethproofs_soundcalc` proof fixture (proved with
                /// the circuit's EthproofsSoundnessCalc config) on the verifier of that mode.
                #[test]
                fn [<$name _ethproofs_soundcalc>]() {
                    run_native(stringify!($name), SecurityLevel::Sec100, SoundnessMode::EthproofsSoundnessCalc);
                }
            )*
        }
    };
}
verifier_common::gkr_circuits!(generate_native_tests);
