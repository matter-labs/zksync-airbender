use std::sync::{LazyLock, OnceLock};

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::definitions::GKRExternalChallenges;
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::gkr::prover_config::{ProverConfig, SoundnessMode};
use prover::merkle_trees::DefaultTreeConstructor;

use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::flatten::flatten_gkr_proof_for_nds;
use crate::prover::definitions::BlakeMode;

const REPO_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/..");

macro_rules! make_circuits {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        vec![$(CircuitData {
            name: stringify!($name),
            production_path: $prod_path,
            security_levels: [SecurityLevel::Sec100],
            prover_configs_cache: [[const { OnceLock::new() }; NUM_SOUNDNESS_MODES]; NUM_SECURITY_LEVELS],
            nds_cache: [const { [const { [const { OnceLock::new() }; NUM_BLAKE_MODES] }; NUM_SOUNDNESS_MODES] }; NUM_SECURITY_LEVELS],
        }),*]
    };
}

/// The circuits with a committed canonical proof.
pub static CIRCUITS: LazyLock<Vec<CircuitData>> =
    LazyLock::new(|| gkr_fixture_circuits!(make_circuits));

/// The canonical fixed-workload 2^23 Compression circuit fixture.
/// It is outside the Standard-profile circuit catalogue.
pub static COMPRESSION: LazyLock<CircuitData> = LazyLock::new(|| {
    CircuitData::new(
        "compression",
        "../circuit_defs/unrolled_circuits/unified_reduced_machine",
    )
});

/// Every circuit with a generated verifier, including those without a canonical proof.
pub static ALL_CIRCUITS: LazyLock<Vec<CircuitData>> =
    LazyLock::new(|| gkr_circuits!(make_circuits));

pub use prover::definitions::SecurityLevel;

const NUM_SECURITY_LEVELS: usize = 1;
const NUM_SOUNDNESS_MODES: usize = SoundnessMode::ALL.len();
const NUM_BLAKE_MODES: usize = BlakeMode::ALL.len();

fn blake_index(blake: BlakeMode) -> usize {
    BlakeMode::ALL
        .iter()
        .position(|m| *m == blake)
        .expect("registered blake mode")
}

fn mode_index(mode: SoundnessMode) -> usize {
    SoundnessMode::ALL
        .iter()
        .position(|m| *m == mode)
        .expect("every soundness mode is listed in SoundnessMode::ALL")
}

/// The name of the generated-verifier folder (under a circuit's
/// `verifier/src/generated/<circuit>/`) and of the `tools/gkr_verifier`
/// circuit-verifier subfolder of a soundness mode. The security level is
/// fixed at 100 bits, so it does not appear in the name.
pub fn verifier_dir_name(mode: SoundnessMode) -> &'static str {
    mode.file_suffix()
}

pub struct CircuitData {
    pub name: &'static str,
    pub production_path: &'static str,
    #[allow(dead_code)]
    security_levels: [SecurityLevel; NUM_SECURITY_LEVELS],
    prover_configs_cache: [[OnceLock<ProverConfig>; NUM_SOUNDNESS_MODES]; NUM_SECURITY_LEVELS],
    nds_cache: [[[OnceLock<(Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>)>;
        NUM_BLAKE_MODES]; NUM_SOUNDNESS_MODES]; NUM_SECURITY_LEVELS],
}

impl CircuitData {
    /// The serialized prover config the circuit definition generated next to
    /// its production layout
    /// (`<production_path>/generated/prover_config_<level>_<mode>.json`,
    /// written by the circuit's artifact generator from its geometry) in the
    /// DEFAULT soundness mode: the config the circuit is proved with, and
    /// thus the one its verifier is generated for.
    pub fn prover_config_path_for(&self, level: SecurityLevel) -> String {
        self.prover_config_path_for_mode(level, SoundnessMode::DEFAULT)
    }

    /// [`Self::prover_config_path_for`] for any soundness mode.
    pub fn prover_config_path_for_mode(&self, level: SecurityLevel, mode: SoundnessMode) -> String {
        format!(
            "{}/generated/prover_config_{}_{}.json",
            self.production_path,
            level.dir_suffix(),
            mode.file_suffix()
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
            prover_configs_cache: [[const { OnceLock::new() }; NUM_SOUNDNESS_MODES];
                NUM_SECURITY_LEVELS],
            nds_cache: [const {
                [const { [const { OnceLock::new() }; NUM_BLAKE_MODES] }; NUM_SOUNDNESS_MODES]
            }; NUM_SECURITY_LEVELS],
        }
    }

    pub fn prover_config_for(&self, level: SecurityLevel) -> &ProverConfig {
        self.prover_config_for_mode(level, SoundnessMode::DEFAULT)
    }

    /// The serialized config of `mode` (see [`Self::prover_config_path_for_mode`]).
    pub fn prover_config_for_mode(
        &self,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> &ProverConfig {
        self.prover_configs_cache[level as usize][mode_index(mode)].get_or_init(|| {
            if self.name == "compression" {
                let trace_len = self.compiled_circuit().trace_len;
                let config = prover::gkr::prover_config::ProofProfile::Compression
                    .prover_config(trace_len.ilog2() as usize, mode);
                assert_eq!(
                    1usize << config.trace_len_log2,
                    trace_len,
                    "Compression profile trace length differs from the compiled circuit"
                );
                return config;
            }
            let path = self.prover_config_path_for_mode(level, mode);
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

    pub fn whir_schedule_for_mode(
        &self,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> &WhirSchedule {
        &self.prover_config_for_mode(level, mode).whir_schedule
    }

    pub fn proof_path_for(&self, level: SecurityLevel) -> String {
        self.proof_path_for_mode(level, SoundnessMode::DEFAULT)
    }

    /// The canonical Sec100 proof fixture proved with the config of `mode`.
    pub fn proof_path_for_mode(&self, _level: SecurityLevel, mode: SoundnessMode) -> String {
        proof_fixtures::circuit_proof(mode.file_suffix(), self.name)
            .to_str()
            .unwrap()
            .to_owned()
    }

    pub fn circuit_path(&self) -> String {
        if self.name == "compression" {
            return CircuitData::new("unified_reduced_machine", self.production_path)
                .circuit_path();
        }
        if self.name == "unified_reduced_machine_2_22" {
            return format!("{}/generated/layout.json", self.production_path);
        }
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

    /// The verifier program's ELF in the default mode (built by
    /// `tools/gkr_verifier/dump_bin.sh`).
    pub fn elf_path_for(&self, level: SecurityLevel) -> String {
        self.elf_path_for_mode(level, SoundnessMode::DEFAULT)
    }

    /// The verifier program's ELF of `mode`:
    /// `tools/gkr_verifier/circuit_verifiers/<mode>/<name>.elf`.
    pub fn elf_path_for_mode(&self, level: SecurityLevel, mode: SoundnessMode) -> String {
        assert_eq!(
            level,
            SecurityLevel::Sec100,
            "the verifier programs are built for 100 bits"
        );
        format!(
            "{}/tools/gkr_verifier/circuit_verifiers/{}/{}.elf",
            REPO_ROOT,
            verifier_dir_name(mode),
            self.name
        )
    }

    /// The circuit's generated-verifier root (`verifier/src/generated/<name>`),
    /// holding one folder per soundness mode ([`Self::generated_dir_for_mode`])
    /// plus the special variants.
    pub fn generated_dir(&self) -> String {
        format!("{}/verifier/src/generated/{}", REPO_ROOT, self.name)
    }

    pub fn generated_dir_for_mode(&self, mode: SoundnessMode) -> String {
        format!("{}/{}", self.generated_dir(), verifier_dir_name(mode))
    }

    pub fn common_generated_dir() -> String {
        format!("{}/verifier/src/generated/common", REPO_ROOT)
    }

    pub fn proof_for(
        &self,
        level: SecurityLevel,
    ) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        self.proof_for_mode(level, SoundnessMode::DEFAULT)
    }

    pub fn proof_for_mode(
        &self,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        let path = self.proof_path_for_mode(level, mode);
        let proof: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
            proof_fixtures::read_file(&path);
        // A stale proof and stale verifier can agree while both lag behind the
        // current config. Check before either native or transpiled verification.
        assert_eq!(
            proof.whir_proof.whir_schedule,
            self.whir_schedule_for_mode(level, mode).clone(),
            "{path}: stale proof fixture; regenerate the matching {mode:?} proofs and per-circuit verifier binaries together"
        );
        proof
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

    /// The fixture proof's ND stream for a verifier built with `blake`
    /// (`crate::BLAKE_MODE` for the verifier compiled into this process, the
    /// ELF's build feature for a RISC-V program).
    pub fn load_nds_for(
        &self,
        level: SecurityLevel,
        blake: BlakeMode,
    ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        self.load_nds_for_mode(level, SoundnessMode::DEFAULT, blake)
    }

    pub fn load_nds_for_mode(
        &self,
        level: SecurityLevel,
        mode: SoundnessMode,
        blake: BlakeMode,
    ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        self.nds_cache[level as usize][mode_index(mode)][blake_index(blake)]
            .get_or_init(|| {
                let circuit = self.compiled_circuit();
                let proof = self.proof_for_mode(level, mode);
                let nds = flatten_gkr_proof_for_nds::<
                    BabyBearField,
                    BabyBearExt4,
                    DefaultTreeConstructor,
                >(&proof, &circuit, blake);
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
