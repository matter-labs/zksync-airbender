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

pub static CIRCUITS: LazyLock<Vec<CircuitData>> = LazyLock::new(|| gkr_circuits!(make_circuits));

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

/// Suffix of the (level, mode) fixtures that predate the soundness modes —
/// proof files and flamegraphs: the DEFAULT mode keeps the plain `sec_100`
/// names of the production artifacts, every other mode appends its name.
pub fn fixture_suffix(level: SecurityLevel, mode: SoundnessMode) -> String {
    if mode == SoundnessMode::DEFAULT {
        level.dir_suffix().to_string()
    } else {
        format!("{}_{}", level.dir_suffix(), mode.file_suffix())
    }
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
    /// A circuit that is not in the [`gkr_circuits!`] registry (so no registry-driven test,
    /// verifier module or fixture is generated for it), addressed by the same paths as a
    /// registered one: `production_path` is its circuit crate relative to the repository
    /// root's children (`"../circuit_defs/..."`).
    pub fn unregistered(name: &'static str, production_path: &'static str) -> Self {
        CircuitData {
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

    /// The proof fixture proved with the config of `mode`
    /// (`prover/test_proofs/<name>_<fixture_suffix>_gkr_proof.json`, see
    /// [`fixture_suffix`]).
    pub fn proof_path_for_mode(&self, level: SecurityLevel, mode: SoundnessMode) -> String {
        format!(
            "{}/prover/test_proofs/{}_{}_gkr_proof.json",
            REPO_ROOT,
            self.name,
            fixture_suffix(level, mode)
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
        deserialize_from_file(&self.proof_path_for_mode(level, mode))
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

/// The packed-base-commitment test fixture: the `blake2_with_extended_control`
/// delegation circuit (2^20 trace) proved with `pack_log2 = 4`, so every
/// committed column is a 2^24 multilinear and WHIR runs the 2^24 schedule.
pub mod packed_fixture {
    use super::*;

    pub const CIRCUIT_NAME: &str = "blake2_with_extended_control";
    pub const PACK_LOG2: usize = 4;
    /// Output dir (under the circuit's generated dir) of the packed verifier:
    /// a pessimistic-conjecture variant.
    pub const DIR_SUFFIX: &str = "pessimistic_conjecture_pack4";

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

    /// The packed verifier program:
    /// `circuit_verifiers/pessimistic_conjecture/blake2_with_extended_control_pack4.elf`.
    pub fn elf_path() -> String {
        format!(
            "{}/tools/gkr_verifier/circuit_verifiers/{}/{}_pack{}.elf",
            REPO_ROOT,
            verifier_dir_name(SoundnessMode::PessimisticConjecture),
            CIRCUIT_NAME,
            PACK_LOG2
        )
    }

    pub fn proof() -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        deserialize_from_file(&proof_path())
    }

    pub fn load_nds(
        blake: BlakeMode,
    ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        let circuit = circuit().compiled_circuit();
        let proof = proof();
        let nds = flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
            &proof, &circuit, blake,
        );
        (nds, proof.external_challenges)
    }
}

/// The VIRTUAL-PACKING test fixture: the `blake2_with_extended_control`
/// delegation circuit (2^20 trace) proved with the virtual-packing base round
/// (`fold_log2 = 0`: one value per column per base leaf, no round-0 sumcheck,
/// the batched polynomial re-committed as intermediate oracle 0 at the same
/// domain size).
pub mod virtual_packing_fixture {
    use super::*;

    pub const CIRCUIT_NAME: &str = "blake2_with_extended_control";
    /// Output dir (under the circuit's generated dir) of the virtual-packing
    /// verifier: a pessimistic-conjecture variant.
    pub const DIR_SUFFIX: &str = "pessimistic_conjecture_virtual";

    pub fn circuit() -> &'static CircuitData {
        CIRCUITS
            .iter()
            .find(|c| c.name == CIRCUIT_NAME)
            .expect("virtual-packing fixture circuit is registered")
    }

    /// The 2^20 sec-100 config with the virtual-packing twin of its WHIR
    /// schedule — exactly the config the prover's
    /// `gkr_blake_delegation_virtual_packing_test_sec_100` proves the fixture with.
    pub fn prover_config() -> ProverConfig {
        prover::gkr::prover_config::example_configs::virtual_packing_config_for_security_level_under_pessimistic_conjecture(
            20,
            SecurityLevel::Sec100,
        )
    }

    pub fn proof_path() -> String {
        format!(
            "{}/prover/test_proofs/{}_sec_100_virtual_gkr_proof.json",
            REPO_ROOT, CIRCUIT_NAME
        )
    }

    pub fn generated_dir() -> String {
        format!("{}/{}", circuit().generated_dir(), DIR_SUFFIX)
    }

    pub fn proof() -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        deserialize_from_file(&proof_path())
    }

    pub fn load_nds(
        blake: BlakeMode,
    ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
        let circuit = circuit().compiled_circuit();
        let proof = proof();
        let nds = flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
            &proof, &circuit, blake,
        );
        (nds, proof.external_challenges)
    }
}

/// The blake base-round comparison sweep fixtures: the
/// `blake2_with_extended_control` delegation circuit (2^20 trace) proved with
/// every physical packing `2^0 ..= 2^4` and two (`fold_log2 = 1`) or one
/// (`fold_log2 = 0`, virtual packing) value(s) per committed column per base
/// leaf. Names follow the prover's `BaseCommitmentVariant::proof_name_infix`:
/// `sec_100`, `sec_100_pack{k}`, `sec_100_virtual`, `sec_100_pack{k}_virtual`.
pub mod blake_variants {
    use super::*;

    pub const CIRCUIT_NAME: &str = "blake2_with_extended_control";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct BlakeVariant {
        pub pack_log2: usize,
        /// `1`: two values per column per base leaf (the current mode);
        /// `0`: one value (virtual packing).
        pub fold_log2: usize,
    }

    impl BlakeVariant {
        /// Every (packing, fold) point of the sweep, packing-major.
        pub fn all() -> Vec<Self> {
            (0..=4)
                .flat_map(|pack_log2| {
                    [
                        Self {
                            pack_log2,
                            fold_log2: 1,
                        },
                        Self {
                            pack_log2,
                            fold_log2: 0,
                        },
                    ]
                })
                .collect()
        }

        /// `"_pack{k}"` (two values per leaf, `k = 0` included so that the
        /// sweep never names the circuit's OWN production fixture, which is
        /// the plain `sec_100`), `"_virtual"`, `"_pack{k}_virtual"`.
        pub fn infix(&self) -> String {
            let mut infix = String::new();
            if self.pack_log2 > 0 || self.fold_log2 == 1 {
                infix.push_str(&format!("_pack{}", self.pack_log2));
            }
            if self.fold_log2 == 0 {
                infix.push_str("_virtual");
            }
            infix
        }

        /// Output dir under the circuit's generated dir (the sweep is a
        /// pessimistic-conjecture variant): `pessimistic_conjecture{infix}`.
        pub fn dir_suffix(&self) -> String {
            format!(
                "{}{}",
                verifier_dir_name(SoundnessMode::PessimisticConjecture),
                self.infix()
            )
        }

        /// `blake2_with_extended_control_sec_100{infix}`: the proof fixture
        /// and flamegraph stem.
        pub fn name(&self) -> String {
            format!("{}_sec_100{}", CIRCUIT_NAME, self.infix())
        }

        pub fn circuit() -> &'static CircuitData {
            CIRCUITS
                .iter()
                .find(|c| c.name == CIRCUIT_NAME)
                .expect("blake sweep circuit is registered")
        }

        pub fn prover_config(&self) -> ProverConfig {
            use prover::gkr::prover_config::example_configs::*;
            match self.fold_log2 {
                1 => packed_config_for_security_level_under_pessimistic_conjecture(
                    20,
                    self.pack_log2,
                    SecurityLevel::Sec100,
                ),
                0 => virtual_packed_config_for_security_level_under_pessimistic_conjecture(
                    20,
                    self.pack_log2,
                    SecurityLevel::Sec100,
                ),
                other => panic!("the blake sweep covers fold_log2 0 and 1, not {other}"),
            }
        }

        pub fn proof_path(&self) -> String {
            format!(
                "{}/prover/test_proofs/{}_gkr_proof.json",
                REPO_ROOT,
                self.name()
            )
        }

        pub fn generated_dir(&self) -> String {
            format!("{}/{}", Self::circuit().generated_dir(), self.dir_suffix())
        }

        /// The RISC-V verifier binaries `tools/gkr_verifier/<name>.{bin,text,elf}`.
        /// The variant's verifier program (built by `tools/gkr_verifier/dump_bin.sh`):
        /// `circuit_verifiers/pessimistic_conjecture/blake2_with_extended_control{infix}.elf`.
        pub fn elf_path(&self) -> String {
            format!(
                "{}/tools/gkr_verifier/circuit_verifiers/{}/{}{}.elf",
                REPO_ROOT,
                verifier_dir_name(SoundnessMode::PessimisticConjecture),
                CIRCUIT_NAME,
                self.infix()
            )
        }

        pub fn proof(&self) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
            deserialize_from_file(&self.proof_path())
        }

        pub fn load_nds(
            &self,
            blake: BlakeMode,
        ) -> (Vec<u32>, GKRExternalChallenges<BabyBearField, BabyBearExt4>) {
            let circuit = Self::circuit().compiled_circuit();
            let proof = self.proof();
            let nds =
                flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &proof, &circuit, blake,
                );
            (nds, proof.external_challenges)
        }
    }
}

#[cfg(test)]
mod fixture_maintenance {
    use super::*;

    /// Rewrite every circuit's serialized prover configs
    /// (`<circuit>/generated/prover_config_<level>_<mode>.json`) in the
    /// CURRENT `ProverConfig` layout: read each back (the decoder accepts the
    /// legacy layout too) and serialize it exactly as
    /// `circuit_common::save_prover_configs` does. Run after a `ProverConfig`
    /// / `WhirSchedule` layout change:
    /// `cargo test -p verifier_common --lib -- --ignored rewrite_prover_config_fixtures_in_current_layout`.
    /// (The configs' CONTENT is regenerated from the circuit geometries by the
    /// `setups` crate's `regenerate_prover_config_fixtures` test.)
    #[test]
    #[ignore]
    fn rewrite_prover_config_fixtures_in_current_layout() {
        for circuit in CIRCUITS.iter() {
            for level in SecurityLevel::ALL.iter() {
                for mode in SoundnessMode::ALL.iter() {
                    let path = circuit.prover_config_path_for_mode(*level, *mode);
                    let config: ProverConfig = deserialize_from_file(&path);
                    config.validate_for_whir_message_size(config.whir_message_size_log2());
                    let mut dst = std::fs::File::create(&path).unwrap();
                    serde_json::to_writer_pretty(&mut dst, &config).unwrap();
                }
            }
        }
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
