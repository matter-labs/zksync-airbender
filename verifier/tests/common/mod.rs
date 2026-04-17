pub use verifier_common::test_circuits::{CircuitData, CIRCUITS};

use verifier_common::errors::DebugErrorCreator;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

pub const VERIFIER_STACK_SIZE: usize = 1 << 27;

macro_rules! define_dispatch {
    ($($name:ident: $schedule:ident: $layout_suffix:expr),* $(,)?) => {
        macro_rules! with_circuit {
            ($circuit_name:expr, |$m:ident| $body:expr) => {
                match $circuit_name {
                    $(stringify!($name) => {
                        use verifier::$name as $m;
                        $body
                    })*
                    other => panic!("unknown circuit: {}", other),
                }
            };
        }
    };
}
verifier_common::gkr_circuits!(define_dispatch);

pub fn load_nds(name: &str) -> Vec<u32> {
    circuit_by_name(name).load_nds()
}

pub fn binary_paths(name: &str) -> (String, String, String) {
    circuit_by_name(name).binary_paths()
}

pub fn circuit_by_name(name: &str) -> &'static CircuitData {
    CIRCUITS
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("unknown circuit: {}", name))
}

/// Run the verifier on the given NDS, treating both Err returns and panics as rejection.
/// Returns true if verification passed, false if rejected.
pub fn verify_nds(name: &str, nds: Vec<u32>) -> bool {
    let prev_hook = std::panic::take_hook();
    let panic_msg = std::sync::Arc::new(std::sync::Mutex::new(None::<String>));
    let panic_msg_clone = panic_msg.clone();
    std::panic::set_hook(Box::new(move |info| {
        *panic_msg_clone.lock().unwrap() = Some(format!("{}", info));
    }));

    let accepted = std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("verify_{}", name))
            .stack_size(VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>()
                        .map_err(|e| format!("{:?}", e))
                })
            })
            .expect("failed to spawn thread");

        match handle.join() {
            Ok(Ok(())) => true,
            Ok(Err(e)) => {
                println!("  [verify] {} rejected via error: {}", name, e);
                false
            }
            Err(_) => false,
        }
    });

    std::panic::set_hook(prev_hook);

    if !accepted {
        if let Some(msg) = panic_msg.lock().unwrap().take() {
            println!("  [verify] {} rejected via panic: {}", name, msg);
        }
    }

    accepted
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
