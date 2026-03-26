use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;

/// Single source of truth for the circuit list.
/// Adding a new circuit = add one identifier here.
/// Keep in sync with: tools/gkr_verifier/Cargo.toml features
///                     tools/gkr_verifier/dump_bin.sh CIRCUITS
macro_rules! define_circuits {
    ($($circuit:ident),* $(,)?) => {
        pub const CIRCUITS: &[&str] = &[$(stringify!($circuit)),*];

        /// Dispatch to the right generated module for the given circuit name.
        macro_rules! with_circuit {
            ($name:expr, |$mod_var:ident| $body:expr) => {
                match $name {
                    $(stringify!($circuit) => {
                        use verifier::$circuit as $mod_var;
                        $body
                    })*
                    other => panic!("unknown circuit: {}", other),
                }
            };
        }
        pub(crate) use with_circuit;
    };
}

define_circuits!(add_sub_lui_auipc_mop, jump_branch_slt, shift_binop,);

pub fn proof_path(name: &str) -> String {
    format!("../prover/test_proofs/{}_gkr_proof.json", name)
}

pub fn circuit_path(name: &str) -> String {
    format!(
        "../cs/compiled_circuits/{}_preprocessed_layout_gkr.json",
        name
    )
}

pub fn binary_paths(name: &str) -> (String, String, String) {
    let base = format!("../tools/gkr_verifier/{}", name);
    (
        format!("{}.bin", base),
        format!("{}.text", base),
        format!("{}.elf", base),
    )
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src =
        std::fs::File::open(filename).unwrap_or_else(|_| panic!("{} doesn't exist", filename));
    serde_json::from_reader(src).unwrap()
}

/// Load a circuit's proof + compiled circuit, flatten into NDS u32 words.
pub fn load_nds(name: &str) -> Vec<u32> {
    let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        deserialize_from_file(&proof_path(name));
    let compiled_circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path(name));
    let whir_schedule = WhirSchedule::default_for_tests_80_bits();
    flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        &proof,
        &compiled_circuit,
        &whir_schedule,
    )
}
