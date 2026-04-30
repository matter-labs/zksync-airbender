#[macro_use]
mod common;

use common::SecurityLevel;
use verifier_common::errors::DebugErrorCreator;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

fn run_native(name: &str, level: SecurityLevel) {
    let (nds, external_challenges) = common::load_nds(name, level);
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("gkr verifier {} {:?}", name, level))
            .stack_size(common::VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, level, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>(&external_challenges)
                        .unwrap_or_else(|e| panic!("{} {:?} failed: {:?}", name, level, e));
                });
            })
            .expect("failed to spawn verifier thread");

        match handle.join() {
            Ok(()) => println!("{} {:?}: verification passed", name, level),
            Err(e) => std::panic::resume_unwind(e),
        }
    });
}

macro_rules! generate_native_tests {
    ($($name:ident: $schedule_80:ident: $schedule_100:ident: $layout_suffix:expr),* $(,)?) => {
        paste::paste! {
            $(
                #[cfg(feature = "security_80")]
                #[test]
                fn [<$name _sec_80>]() {
                    run_native(stringify!($name), SecurityLevel::Sec80);
                }
                #[cfg(feature = "security_100")]
                #[test]
                fn [<$name _sec_100>]() {
                    run_native(stringify!($name), SecurityLevel::Sec100);
                }
            )*
        }
    };
}
verifier_common::gkr_circuits!(generate_native_tests);
