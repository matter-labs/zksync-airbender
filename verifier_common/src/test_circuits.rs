use std::sync::{LazyLock, OnceLock};

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::definitions::GKRExternalChallenges;
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::DefaultTreeConstructor;

use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::flatten::flatten_gkr_proof_for_nds;

const REPO_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/..");

macro_rules! make_circuits {
    ($($name:ident: $schedule_fn_80:ident: $schedule_fn_100:ident: $layout_suffix:expr),* $(,)?) => {
        vec![$(CircuitData {
            name: stringify!($name),
            layout_suffix: $layout_suffix,
            whir_schedule_init: [
                WhirSchedule::$schedule_fn_80,
                WhirSchedule::$schedule_fn_100,
            ],
            whir_schedule_cache: [OnceLock::new(), OnceLock::new()],
            nds_cache: [OnceLock::new(), OnceLock::new()],
        }),*]
    };
}

pub static CIRCUITS: LazyLock<Vec<CircuitData>> = LazyLock::new(|| gkr_circuits!(make_circuits));

pub use prover::definitions::SecurityLevel;

const NUM_SECURITY_LEVELS: usize = 2;

pub struct CircuitData {
    pub name: &'static str,
    pub layout_suffix: &'static str,
    whir_schedule_init: [fn() -> WhirSchedule; NUM_SECURITY_LEVELS],
    whir_schedule_cache: [OnceLock<WhirSchedule>; NUM_SECURITY_LEVELS],
    nds_cache: [OnceLock<(Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>)>;
        NUM_SECURITY_LEVELS],
}

impl CircuitData {
    pub fn whir_schedule_for(&self, level: SecurityLevel) -> &WhirSchedule {
        let idx = level as usize;
        self.whir_schedule_cache[idx].get_or_init(self.whir_schedule_init[idx])
    }

    pub fn proof_path_for(&self, level: SecurityLevel) -> String {
        format!(
            "{}/prover/test_proofs/{}_{}_gkr_proof.json",
            REPO_ROOT,
            self.name,
            level.dir_suffix()
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

    pub fn binary_paths_for(&self, level: SecurityLevel) -> (String, String, String) {
        let base = format!(
            "{}/tools/gkr_verifier/{}_{}",
            REPO_ROOT,
            self.name,
            level.dir_suffix()
        );
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

    pub fn proof_for(
        &self,
        level: SecurityLevel,
    ) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        deserialize_from_file(&self.proof_path_for(level))
    }

    pub fn compiled_circuit(&self) -> GKRCircuitArtifact<BabyBearField> {
        deserialize_from_file(&self.circuit_path())
    }

    pub fn load_nds_for(
        &self,
        level: SecurityLevel,
    ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        self.nds_cache[level as usize]
            .get_or_init(|| {
                let circuit = self.compiled_circuit();
                let inits_and_teardowns_top_bits: Vec<u32> =
                    (0..circuit.memory_layout.teardown_sets.len())
                        .map(|i| i as u32)
                        .collect();
                let proof = self.proof_for(level);
                let nds = flatten_gkr_proof_for_nds::<
                    BabyBearField,
                    BabyBearExt4,
                    DefaultTreeConstructor,
                >(
                    &proof,
                    &circuit,
                    self.whir_schedule_for(level),
                    &inits_and_teardowns_top_bits,
                );
                let challenges = proof.external_challenges;

                (nds, challenges)
            })
            .clone()
    }
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src =
        std::fs::File::open(filename).unwrap_or_else(|_| panic!("{} doesn't exist", filename));
    serde_json::from_reader(src).unwrap()
}
