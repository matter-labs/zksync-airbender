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
            security_levels: [SecurityLevel::Sec100],
            prover_configs_cache: [OnceLock::new()],
            nds_cache: [OnceLock::new()],
        }),*]
    };
}

pub static CIRCUITS: LazyLock<Vec<CircuitData>> = LazyLock::new(|| gkr_circuits!(make_circuits));

pub use prover::definitions::SecurityLevel;

const NUM_SECURITY_LEVELS: usize = 1;

pub struct CircuitData {
    pub name: &'static str,
    pub production_path: &'static str,
    #[allow(dead_code)]
    security_levels: [SecurityLevel; NUM_SECURITY_LEVELS],
    prover_configs_cache: [OnceLock<ProverConfig>; NUM_SECURITY_LEVELS],
    nds_cache: [OnceLock<(Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>)>;
        NUM_SECURITY_LEVELS],
}

impl CircuitData {
    /// The serialized prover config the circuit definition generated next to
    /// its production layout (`<production_path>/generated/prover_config_<level>.json`,
    /// written by the circuit's artifact generator from its `prover_config`):
    /// the config the circuit is proved with, and thus the one its verifier is
    /// generated for.
    pub fn prover_config_path_for(&self, level: SecurityLevel) -> String {
        format!(
            "{}/generated/prover_config_{}.json",
            self.production_path,
            level.dir_suffix()
        )
    }

    /// A circuit outside the `gkr_circuits!` catalogue (its production
    /// crate and `cs/compiled_circuits/<name>_layout*_gkr.json` artifacts
    /// exist, but no standard per-level verifier is generated for it).
    pub fn new(name: &'static str, production_path: &'static str) -> Self {
        Self {
            name,
            production_path,
            security_levels: [SecurityLevel::Sec100],
            prover_configs_cache: [OnceLock::new()],
            nds_cache: [OnceLock::new()],
        }
    }

    pub fn prover_config_for(&self, level: SecurityLevel) -> &ProverConfig {
        let idx = level as usize;
        self.prover_configs_cache[idx].get_or_init(|| {
            let path = self.prover_config_path_for(level);
            let config: ProverConfig = deserialize_from_file(&path);
            assert_eq!(
                1usize << config.trace_len_log2,
                self.compiled_circuit().trace_len,
                "{path}: trace length differs from the compiled circuit's — regenerate the artifacts"
            );
            config
        })
    }

    pub fn whir_schedule_for(&self, level: SecurityLevel) -> &WhirSchedule {
        &self.prover_config_for(level).whir_schedule
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
                wip_layout == prod_layout,
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

/// The packed-base-commitment test fixture: the `blake2_with_extended_control`
/// delegation circuit (2^20 trace) proved with `pack_log2 = 4`, so every
/// committed column is a 2^24 multilinear and WHIR runs the 2^24 schedule.
pub mod packed_fixture {
    use super::*;

    pub const CIRCUIT_NAME: &str = "blake2_with_extended_control";
    pub const PACK_LOG2: usize = 4;
    /// Output dir suffix (under the circuit's generated dir) of the packed verifier.
    pub const DIR_SUFFIX: &str = "sec_100_pack4";

    pub fn circuit() -> &'static CircuitData {
        CIRCUITS
            .iter()
            .find(|c| c.name == CIRCUIT_NAME)
            .expect("packed fixture circuit is registered")
    }

    /// The 2^20 sec-100 config's GKR/sumcheck schedules with the 2^24 config's
    /// WHIR side (the packed message is `2^(20 + 4)`) — exactly the config the
    /// prover's `gkr_blake_delegation_packed_test_sec_100` proves the fixture with.
    pub fn prover_config() -> ProverConfig {
        prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(
            20,
            PACK_LOG2,
            SecurityLevel::Sec100,
        )
    }

    pub fn proof_path() -> String {
        format!(
            "{}/prover/test_proofs/{}_sec_100_pack4_gkr_proof.json",
            REPO_ROOT, CIRCUIT_NAME
        )
    }

    pub fn generated_dir() -> String {
        format!("{}/{}", circuit().generated_dir(), DIR_SUFFIX)
    }

    pub fn proof() -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        deserialize_from_file(&proof_path())
    }

    pub fn load_nds() -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        let circuit = circuit().compiled_circuit();
        let proof = proof();
        let nds = flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
            &proof, &circuit,
        );
        (nds, proof.external_challenges)
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
