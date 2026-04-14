pub use verifier_common::test_circuits::{CircuitData, CIRCUITS};

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
