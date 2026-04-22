use std::sync::{LazyLock, OnceLock};

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::DefaultTreeConstructor;

use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::flatten::flatten_gkr_proof_for_nds;

const REPO_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/..");

macro_rules! make_circuits {
    ($($name:ident: $schedule_fn:ident: $layout_suffix:expr),* $(,)?) => {
        vec![$(CircuitData {
            name: stringify!($name),
            layout_suffix: $layout_suffix,
            whir_schedule: WhirSchedule::$schedule_fn(),
            nds_cache: OnceLock::new(),
        }),*]
    };
}

pub static CIRCUITS: LazyLock<Vec<CircuitData>> = LazyLock::new(|| gkr_circuits!(make_circuits));

pub struct CircuitData {
    pub name: &'static str,
    pub layout_suffix: &'static str,
    pub whir_schedule: WhirSchedule,
    nds_cache: OnceLock<Vec<u32>>,
}

impl CircuitData {
    pub fn whir_schedule(&self) -> &WhirSchedule {
        &self.whir_schedule
    }

    pub fn proof_path(&self) -> String {
        format!(
            "{}/prover/test_proofs/{}_gkr_proof.json",
            REPO_ROOT, self.name
        )
    }

    pub fn circuit_path(&self) -> String {
        if self.name == "inits_and_teardowns" {
            format!(
                "{}/cs/compiled_circuits/{}{}_no_caches_gkr.json",
                REPO_ROOT, self.name, self.layout_suffix
            )
        } else {
            #[cfg(feature = "no_caches")]
            let suffix = "_no_caches";
            #[cfg(not(feature = "no_caches"))]
            let suffix = "";
            format!(
                "{}/cs/compiled_circuits/{}{}{}_gkr.json",
                REPO_ROOT, self.name, self.layout_suffix, suffix
            )
        }
    }

    pub fn binary_paths(&self) -> (String, String, String) {
        let base = format!("{}/tools/gkr_verifier/{}", REPO_ROOT, self.name);
        (
            format!("{}.bin", base),
            format!("{}.text", base),
            format!("{}.elf", base),
        )
    }

    pub fn generated_dir(&self) -> String {
        format!("{}/verifier/src/generated/{}", REPO_ROOT, self.name)
    }

    pub fn common_generated_dir() -> String {
        format!("{}/verifier/src/generated/common", REPO_ROOT)
    }

    pub fn proof(&self) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        deserialize_from_file(&self.proof_path())
    }

    pub fn compiled_circuit(&self) -> GKRCircuitArtifact<BabyBearField> {
        deserialize_from_file(&self.circuit_path())
    }

    pub fn load_nds(&self) -> Vec<u32> {
        self.nds_cache
            .get_or_init(|| {
                let circuit = self.compiled_circuit();
                let inits_and_teardowns_top_bits: Vec<u32> =
                    (0..circuit.memory_layout.teardown_sets.len())
                        .map(|i| i as u32)
                        .collect();
                flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &self.proof(),
                    &circuit,
                    self.whir_schedule(),
                    &inits_and_teardowns_top_bits,
                )
            })
            .clone()
    }
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src =
        std::fs::File::open(filename).unwrap_or_else(|_| panic!("{} doesn't exist", filename));
    serde_json::from_reader(src).unwrap()
}
