use std::sync::{LazyLock, OnceLock};

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::definitions::GKRExternalChallenges;
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::gkr::prover_config::ProverConfig;
use prover::merkle_trees::DefaultTreeConstructor;

use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::flatten::flatten_gkr_proof_for_nds;

const REPO_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/..");

macro_rules! make_circuits {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        vec![$(CircuitData {
            name: stringify!($name),
            production_path: $prod_path,
            prover_configs_cache: [OnceLock::new(), OnceLock::new()],
            nds_cache: [OnceLock::new(), OnceLock::new()],
        }),*]
    };
}

pub static CIRCUITS: LazyLock<Vec<CircuitData>> = LazyLock::new(|| gkr_circuits!(make_circuits));

pub use prover::definitions::SecurityLevel;

const NUM_SECURITY_LEVELS: usize = 2;

pub struct CircuitData {
    pub name: &'static str,
    pub production_path: &'static str,
    prover_configs_cache: [OnceLock<ProverConfig>; NUM_SECURITY_LEVELS],
    nds_cache: [OnceLock<(Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>)>;
        NUM_SECURITY_LEVELS],
}

impl CircuitData {
    pub fn prover_config_for(&self, level: SecurityLevel) -> &ProverConfig {
        let idx = level as usize;
        self.prover_configs_cache[idx].get_or_init(|| prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(self.compiled_circuit().trace_len.trailing_zeros() as usize, level))
    }

    pub fn whir_schedule_for(&self, level: SecurityLevel) -> &WhirSchedule {
        let idx = level as usize;
        &self.prover_configs_cache[idx].get_or_init(|| prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(self.compiled_circuit().trace_len.trailing_zeros() as usize, level)).whir_schedule
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
                "{}/cs/compiled_circuits/{}_layout_no_caches_gkr.json",
                REPO_ROOT, self.name,
            )
        } else {
            #[cfg(feature = "no_caches")]
            let suffix = "_no_caches";
            #[cfg(not(feature = "no_caches"))]
            let suffix = "";
            format!(
                "{}/cs/compiled_circuits/{}_layout{}_gkr.json",
                REPO_ROOT, self.name, suffix
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
        let wip_layout: GKRCircuitArtifact<BabyBearField> =
            deserialize_from_file(&self.circuit_path());
        let prod_layout_path = format!("{}/generated/layout.json", self.production_path);
        if let Ok(prod_layout) = try_deserialize_from_file(&prod_layout_path) {
            assert!(
                &wip_layout == &prod_layout,
                "layouts differ in debug and production files, that may lead to subtle bugs: {} vs {}",
                self.circuit_path(),
                prod_layout_path,
            );
        } else {
            println!("No production layout for circuit {}", self.name);
        }
        wip_layout
    }

    pub fn load_nds_for(
        &self,
        level: SecurityLevel,
    ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        self.nds_cache[level as usize]
            .get_or_init(|| {
                let circuit = self.compiled_circuit();
                let proof = self.proof_for(level);
                let nds = flatten_gkr_proof_for_nds::<
                    BabyBearField,
                    BabyBearExt4,
                    DefaultTreeConstructor,
                >(&proof, &circuit);
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

fn try_deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> Result<T, ()> {
    let src = std::fs::File::open(filename).map_err(|_| ())?;
    Ok(serde_json::from_reader(src).unwrap())
}
