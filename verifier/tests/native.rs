#![cfg(feature = "gkr_verify")]

mod common;

use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

fn run_native(name: &str) {
    let nds = common::load_nds(name);
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("gkr verifier {}", name))
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                common::with_circuit!(name, |m| {
                    m::verify_all::<ThreadLocalBasedSource>()
                        .unwrap_or_else(|e| panic!("{} failed: {:?}", name, e));
                });
            })
            .expect("failed to spawn verifier thread");

        match handle.join() {
            Ok(()) => println!("{}: verification passed", name),
            Err(e) => std::panic::resume_unwind(e),
        }
    });
}

macro_rules! native_tests {
    ($($circuit:ident),* $(,)?) => {
        $(
            #[test]
            fn $circuit() {
                run_native(stringify!($circuit));
            }
        )*
    };
}

native_tests!(add_sub_lui_auipc_mop, jump_branch_slt, shift_binop,);
