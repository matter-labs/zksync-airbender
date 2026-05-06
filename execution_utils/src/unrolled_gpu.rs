use crate::get_padded_binary;
use crate::unified_recursion_target_family_proofs;
use crate::unrolled::{
    compute_setup_for_machine_configuration, flatten_proof_into_responses_for_unrolled_recursion,
    UnrolledProgramProof, UnrolledProgramSetup,
};
use crate::verifier_binaries;
use crate::{RecursionArtifact, RecursionLayer};
use gpu_prover::{
    execution::prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration},
    machine_type::MachineType,
};
use setups::{
    binary_u8_to_u32, get_unified_circuit_artifact_for_machine_type,
    get_unrolled_circuits_artifacts_for_machine_type, pad_bytecode_bytes_for_proving,
    pad_bytecode_for_proving, read_binary, CompiledCircuitsSet,
};
use verifier_common::security_100::Security100Marker;
use verifier_common::security_80::Security80Marker;
use verifier_common::SecurityModel;

use crate::unified_circuit::{
    compute_unified_setup_for_machine_configuration,
    flatten_proof_into_responses_for_unified_recursion,
};
use gpu_prover::execution::prover::ProveResult;
use log::info;
use riscv_transpiler::common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use riscv_transpiler::{
    abstractions::non_determinism::QuasiUARTSource,
    cycle::{IMStandardIsaConfigWithUnsignedMulDiv, IWithoutByteAccessIsaConfigWithDelegation},
};
use std::collections::BTreeMap;
use std::{io::Read, path::Path};

impl From<ProveResult> for UnrolledProgramProof {
    fn from(value: ProveResult) -> Self {
        UnrolledProgramProof {
            final_pc: value.final_pc,
            final_timestamp: value.final_timestamp,
            circuit_families_proofs: value.circuit_families_proofs,
            inits_and_teardowns_proofs: value.inits_and_teardowns_proofs,
            delegation_proofs: value.delegation_proofs,
            register_final_values: value.register_final_values,
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
            pow_challenge: value.pow_challenge,
        }
    }
}

pub fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(&format!("{filename}"));
    serde_json::from_reader(src).unwrap()
}

pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &Path) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn load_binary_from_path(path: &String) -> Vec<u32> {
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    get_padded_binary(&buffer)
}

#[repr(usize)]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum UnrolledProverLevel {
    Base = 0,
    RecursionUnrolled = 1,
    RecursionUnified = 2,
}

/// Per-level setup data extracted from an `UnrolledProver`.
///
/// `setup` and `compiled_layouts` are deterministic functions of the layer's
/// (binary, text) inputs and the embedded verifier binaries shipped with this
/// crate, but they are extremely expensive to compute. Caching them lets a
/// freshly-started prover skip the warm-up.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProverLevelSetup {
    pub setup: UnrolledProgramSetup,
    pub compiled_layouts: CompiledCircuitsSet,
}

/// Snapshot of every level's setup data, suitable for serializing to disk and
/// re-feeding into `UnrolledProver::new_with_cache` on a subsequent run.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProverCache {
    pub security: SecurityModel,
    pub max_level: UnrolledProverLevel,
    pub levels: BTreeMap<UnrolledProverLevel, UnrolledProverLevelSetup>,
}

#[derive(Debug)]
pub enum UnrolledProverCacheError {
    SecurityMismatch {
        cached: SecurityModel,
        expected: SecurityModel,
    },
    MaxLevelTooLow {
        cached: UnrolledProverLevel,
        expected: UnrolledProverLevel,
    },
    MissingLevel(UnrolledProverLevel),
}

impl std::fmt::Display for UnrolledProverCacheError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SecurityMismatch { cached, expected } => write!(
                f,
                "setup cache built for {cached:?} cannot serve a {expected:?} prover",
            ),
            Self::MaxLevelTooLow { cached, expected } => write!(
                f,
                "setup cache supports up to {cached:?} but {expected:?} was requested",
            ),
            Self::MissingLevel(level) => {
                write!(f, "setup cache is missing required level {level:?}")
            }
        }
    }
}

impl std::error::Error for UnrolledProverCacheError {}

pub struct UnrolledProverLevelData {
    pub binary: Vec<u8>,
    pub text: Vec<u8>,
    pub binary_u32: Vec<u32>,
    pub text_u32: Vec<u32>,
    pub setup: UnrolledProgramSetup,
    pub compiled_layouts: CompiledCircuitsSet,
    pub hash_chain: [u32; 8],
    pub preimage: [u32; 16],
}

pub struct UnrolledProver {
    pub max_level: UnrolledProverLevel,
    pub level_data: BTreeMap<UnrolledProverLevel, UnrolledProverLevelData>,
    pub prover: RuntimeExecutionProver,
}

// `execution_utils` is the first layer that legitimately needs runtime
// security selection, so the enum wrapper lives here instead of inside
// `gpu_prover`.
pub enum RuntimeExecutionProver {
    Security80(ExecutionProver<Security80Marker>),
    Security100(ExecutionProver<Security100Marker>),
}

impl RuntimeExecutionProver {
    fn add_binary(
        &mut self,
        key: usize,
        execution_kind: ExecutionKind,
        machine_type: MachineType,
        binary_image: Vec<u32>,
        text_section: Vec<u32>,
        cycles_bound: Option<u32>,
    ) {
        match self {
            Self::Security80(prover) => prover.add_binary(
                key,
                execution_kind,
                machine_type,
                binary_image,
                text_section,
                cycles_bound,
            ),
            Self::Security100(prover) => prover.add_binary(
                key,
                execution_kind,
                machine_type,
                binary_image,
                text_section,
                cycles_bound,
            ),
        }
    }

    fn commit_memory_and_prove(
        &self,
        batch_id: u64,
        binary_key: usize,
        non_determinism_source: impl riscv_transpiler::vm::NonDeterminismCSRSource + Send + 'static,
    ) -> ProveResult {
        match self {
            Self::Security80(prover) => {
                prover.commit_memory_and_prove(batch_id, binary_key, non_determinism_source)
            }
            Self::Security100(prover) => {
                prover.commit_memory_and_prove(batch_id, binary_key, non_determinism_source)
            }
        }
    }

    fn security(&self) -> SecurityModel {
        match self {
            Self::Security80(prover) => prover.security(),
            Self::Security100(prover) => prover.security(),
        }
    }
}

fn unified_recursion_has_converged(security: SecurityModel, family_proof_count: usize) -> bool {
    // Unified recursion converges once proof shape reaches target size.
    let target = unified_recursion_target_family_proofs(security);
    family_proof_count == target
}

impl UnrolledProver {
    pub fn new(
        security: SecurityModel,
        path_without_bin: &String,
        prover_configuration: ExecutionProverConfiguration,
        max_level: UnrolledProverLevel,
    ) -> Self {
        Self::build_inner(
            security,
            path_without_bin,
            prover_configuration,
            max_level,
            None,
        )
    }

    /// Build a prover, reusing pre-computed setups from `cache` instead of
    /// regenerating them. The cache must have been produced by `dump_cache` on
    /// a prover built with the same security level and binaries; mismatches in
    /// `security` or insufficient `max_level` coverage are rejected up front.
    /// Mismatched binaries cannot be detected here and will manifest as a
    /// proving-time failure — callers are expected to key the on-disk cache
    /// path on a binary fingerprint.
    pub fn new_with_cache(
        security: SecurityModel,
        path_without_bin: &String,
        prover_configuration: ExecutionProverConfiguration,
        max_level: UnrolledProverLevel,
        cache: &UnrolledProverCache,
    ) -> Result<Self, UnrolledProverCacheError> {
        if cache.security != security {
            return Err(UnrolledProverCacheError::SecurityMismatch {
                cached: cache.security,
                expected: security,
            });
        }
        if cache.max_level < max_level {
            return Err(UnrolledProverCacheError::MaxLevelTooLow {
                cached: cache.max_level,
                expected: max_level,
            });
        }
        let required: &[UnrolledProverLevel] = match max_level {
            UnrolledProverLevel::Base => &[UnrolledProverLevel::Base],
            UnrolledProverLevel::RecursionUnrolled => &[
                UnrolledProverLevel::Base,
                UnrolledProverLevel::RecursionUnrolled,
            ],
            UnrolledProverLevel::RecursionUnified => &[
                UnrolledProverLevel::Base,
                UnrolledProverLevel::RecursionUnrolled,
                UnrolledProverLevel::RecursionUnified,
            ],
        };
        for level in required {
            if !cache.levels.contains_key(level) {
                return Err(UnrolledProverCacheError::MissingLevel(*level));
            }
        }
        Ok(Self::build_inner(
            security,
            path_without_bin,
            prover_configuration,
            max_level,
            Some(cache),
        ))
    }

    /// Snapshot per-level setup data so it can be serialized and reloaded via
    /// `new_with_cache` on a subsequent startup.
    pub fn dump_cache(&self) -> UnrolledProverCache {
        let levels = self
            .level_data
            .iter()
            .map(|(&level, data)| {
                (
                    level,
                    UnrolledProverLevelSetup {
                        setup: data.setup.clone(),
                        compiled_layouts: data.compiled_layouts.clone(),
                    },
                )
            })
            .collect();
        UnrolledProverCache {
            security: self.prover.security(),
            max_level: self.max_level,
            levels,
        }
    }

    fn build_inner(
        security: SecurityModel,
        path_without_bin: &String,
        prover_configuration: ExecutionProverConfiguration,
        max_level: UnrolledProverLevel,
        cache: Option<&UnrolledProverCache>,
    ) -> Self {
        let mut prover = match security {
            SecurityModel::Security80 => RuntimeExecutionProver::Security80(ExecutionProver::<
                Security80Marker,
            >::with_configuration_80(
                prover_configuration
            )),
            SecurityModel::Security100 => RuntimeExecutionProver::Security100(
                ExecutionProver::<Security100Marker>::with_configuration_100(prover_configuration),
            ),
        };
        let mut level_data = BTreeMap::new();

        {
            let bin_path = format!("{}.bin", path_without_bin);
            let text_path = format!("{}.text", path_without_bin);
            let (binary, binary_u32) = read_binary(Path::new(&bin_path));
            let (text, text_u32) = read_binary(Path::new(&text_path));
            prover.add_binary(
                UnrolledProverLevel::Base as usize,
                ExecutionKind::Unrolled,
                MachineType::FullUnsigned,
                binary_u32.clone(),
                text_u32.clone(),
                None,
            );
            let (setup, compiled_layouts) =
                match cache.and_then(|c| c.levels.get(&UnrolledProverLevel::Base)) {
                    Some(cached) => {
                        info!("Reusing cached base layer setup");
                        (cached.setup.clone(), cached.compiled_layouts.clone())
                    }
                    None => {
                        info!("Computing base layer setup");
                        let mut padded_binary = binary.clone();
                        pad_bytecode_bytes_for_proving(&mut padded_binary);
                        let mut padded_text = text.clone();
                        pad_bytecode_bytes_for_proving(&mut padded_text);
                        let mut padded_binary_u32 = binary_u32.clone();
                        pad_bytecode_for_proving(&mut padded_binary_u32);
                        let setup = compute_setup_for_machine_configuration::<
                            IMStandardIsaConfigWithUnsignedMulDiv,
                        >(&padded_binary, &padded_text);
                        let compiled_layouts = get_unrolled_circuits_artifacts_for_machine_type::<
                            IMStandardIsaConfigWithUnsignedMulDiv,
                        >(&padded_binary_u32);
                        (setup, compiled_layouts)
                    }
                };
            let (hash_chain, preimage) =
                UnrolledProgramSetup::begin_recursion_chain(&setup.end_params);
            let data = UnrolledProverLevelData {
                binary,
                text,
                binary_u32,
                text_u32,
                setup,
                compiled_layouts,
                hash_chain,
                preimage,
            };
            level_data.insert(UnrolledProverLevel::Base, data);
        }

        if max_level >= UnrolledProverLevel::RecursionUnrolled {
            let binary = verifier_binaries::recursion_artifact(
                security,
                RecursionLayer::Unrolled,
                RecursionArtifact::Bin,
            )
            .to_vec();
            let binary_u32 = binary_u8_to_u32(&binary);
            let text = verifier_binaries::recursion_artifact(
                security,
                RecursionLayer::Unrolled,
                RecursionArtifact::Txt,
            )
            .to_vec();
            let text_u32 = binary_u8_to_u32(&text);
            prover.add_binary(
                UnrolledProverLevel::RecursionUnrolled as usize,
                ExecutionKind::Unrolled,
                MachineType::Reduced,
                binary_u32.clone(),
                text_u32.clone(),
                None,
            );
            let (setup, compiled_layouts) =
                match cache.and_then(|c| c.levels.get(&UnrolledProverLevel::RecursionUnrolled)) {
                    Some(cached) => {
                        info!("Reusing cached recursion-unrolled layer setup");
                        (cached.setup.clone(), cached.compiled_layouts.clone())
                    }
                    None => {
                        info!("Computing recursion in unrolled layer setup");
                        let mut padded_binary = binary.clone();
                        pad_bytecode_bytes_for_proving(&mut padded_binary);
                        let mut padded_text = text.clone();
                        pad_bytecode_bytes_for_proving(&mut padded_text);
                        let mut padded_binary_u32 = binary_u32.clone();
                        pad_bytecode_for_proving(&mut padded_binary_u32);
                        let setup = compute_setup_for_machine_configuration::<
                            IWithoutByteAccessIsaConfigWithDelegation,
                        >(&padded_binary, &padded_text);
                        let compiled_layouts = get_unrolled_circuits_artifacts_for_machine_type::<
                            IWithoutByteAccessIsaConfigWithDelegation,
                        >(&padded_binary_u32);
                        (setup, compiled_layouts)
                    }
                };
            let previous_level_data = &level_data[&UnrolledProverLevel::Base];
            let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
                &setup.end_params,
                &previous_level_data.hash_chain,
                &previous_level_data.preimage,
            );
            let data = UnrolledProverLevelData {
                binary,
                text,
                binary_u32,
                text_u32,
                setup,
                compiled_layouts,
                hash_chain,
                preimage,
            };
            level_data.insert(UnrolledProverLevel::RecursionUnrolled, data);
        }

        if max_level == UnrolledProverLevel::RecursionUnified {
            let binary = verifier_binaries::recursion_artifact(
                security,
                RecursionLayer::Unified,
                RecursionArtifact::Bin,
            )
            .to_vec();
            let binary_u32 = binary_u8_to_u32(&binary);
            let text = verifier_binaries::recursion_artifact(
                security,
                RecursionLayer::Unified,
                RecursionArtifact::Txt,
            )
            .to_vec();
            let text_u32 = binary_u8_to_u32(&text);
            prover.add_binary(
                UnrolledProverLevel::RecursionUnified as usize,
                ExecutionKind::Unified,
                MachineType::Reduced,
                binary_u32.clone(),
                text_u32.clone(),
                None,
            );
            let (setup, compiled_layouts) =
                match cache.and_then(|c| c.levels.get(&UnrolledProverLevel::RecursionUnified)) {
                    Some(cached) => {
                        info!("Reusing cached recursion-unified layer setup");
                        (cached.setup.clone(), cached.compiled_layouts.clone())
                    }
                    None => {
                        info!("Computing recursion in unified layer setup");
                        let mut padded_binary = binary.clone();
                        pad_bytecode_bytes_for_proving(&mut padded_binary);
                        let mut padded_text = text.clone();
                        pad_bytecode_bytes_for_proving(&mut padded_text);
                        let mut padded_binary_u32 = binary_u32.clone();
                        pad_bytecode_for_proving(&mut padded_binary_u32);
                        let setup = compute_unified_setup_for_machine_configuration::<
                            IWithoutByteAccessIsaConfigWithDelegation,
                        >(&padded_binary, &padded_text);
                        let compiled_layouts = get_unified_circuit_artifact_for_machine_type::<
                            IWithoutByteAccessIsaConfigWithDelegation,
                        >(&padded_binary_u32);
                        (setup, compiled_layouts)
                    }
                };
            let previous_level_data = &level_data[&UnrolledProverLevel::RecursionUnrolled];
            let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
                &setup.end_params,
                &previous_level_data.hash_chain,
                &previous_level_data.preimage,
            );
            let data = UnrolledProverLevelData {
                binary,
                text,
                binary_u32,
                text_u32,
                setup,
                compiled_layouts,
                hash_chain,
                preimage,
            };
            level_data.insert(UnrolledProverLevel::RecursionUnified, data);
        }

        Self {
            max_level,
            level_data,
            prover,
        }
    }

    pub fn prove(
        &self,
        batch_id_base: u64,
        source: impl riscv_transpiler::vm::NonDeterminismCSRSource + Send + Sync + 'static,
    ) -> (UnrolledProgramProof, u64) {
        let mut batch_id = batch_id_base * 10;
        info!("Computing proof");

        let (mut proof, cycles) = {
            let binary_key = UnrolledProverLevel::Base as usize;
            let start_time = std::time::Instant::now();
            let result = self
                .prover
                .commit_memory_and_prove(batch_id, binary_key, source);
            let elapsed = start_time.elapsed().as_secs_f64();
            let cycles = (result.final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
            let proof: UnrolledProgramProof = result.into();
            info!(
                "Base layer proof done in {elapsed:.3}s {}",
                proof.debug_info()
            );
            (proof, cycles)
        };

        if self.max_level == UnrolledProverLevel::Base {
            return (proof, cycles);
        }

        let mut unrolled_recursion_layer = 0u64;

        loop {
            batch_id += 1;
            let previous_layer_is_base = unrolled_recursion_layer == 0;
            let previous_level = if previous_layer_is_base {
                UnrolledProverLevel::Base
            } else {
                UnrolledProverLevel::RecursionUnrolled
            };
            let previous_layer_data = &self.level_data[&previous_level];
            let setup = &previous_layer_data.setup;
            let layouts = &previous_layer_data.compiled_layouts;
            let witness = flatten_proof_into_responses_for_unrolled_recursion(
                &proof,
                &setup,
                &layouts,
                previous_layer_is_base,
            );
            let source = QuasiUARTSource::new_with_reads(witness);
            let start_time = std::time::Instant::now();
            let binary_key = UnrolledProverLevel::RecursionUnrolled as usize;
            let result = self
                .prover
                .commit_memory_and_prove(batch_id, binary_key, source);
            let elapsed = start_time.elapsed().as_secs_f64();
            proof = result.into();
            proof.recursion_chain_hash = Some(previous_layer_data.hash_chain);
            proof.recursion_chain_preimage = Some(previous_layer_data.preimage);
            info!(
                "Unrolled recursion layer {unrolled_recursion_layer} proof done in {elapsed:.3}s {}",
                proof.debug_info()
            );
            let (_, _, delegation_proof_count) = proof.get_proof_counts();
            if delegation_proof_count == 1 {
                break;
            }
            unrolled_recursion_layer += 1;
        }

        if self.max_level == UnrolledProverLevel::RecursionUnrolled {
            return (proof, cycles);
        }

        let mut unified_recursion_layer = 0u64;

        loop {
            batch_id += 1;
            let previous_level_is_unrolled = unified_recursion_layer == 0;
            let previous_level = if previous_level_is_unrolled {
                UnrolledProverLevel::RecursionUnrolled
            } else {
                UnrolledProverLevel::RecursionUnified
            };
            let previous_layer_data = &self.level_data[&previous_level];
            let setup = &previous_layer_data.setup;
            let layouts = &previous_layer_data.compiled_layouts;
            let witness = flatten_proof_into_responses_for_unified_recursion(
                &proof,
                &setup,
                &layouts,
                previous_level_is_unrolled,
            );
            let source = QuasiUARTSource::new_with_reads(witness);
            let start_time = std::time::Instant::now();
            let binary_key = UnrolledProverLevel::RecursionUnified as usize;
            let result = self
                .prover
                .commit_memory_and_prove(batch_id, binary_key, source);
            let elapsed = start_time.elapsed().as_secs_f64();
            proof = result.into();
            proof.recursion_chain_hash = Some(previous_layer_data.hash_chain);
            proof.recursion_chain_preimage = Some(previous_layer_data.preimage);
            info!(
                "Unified recursion layer {unified_recursion_layer} proof done in {elapsed:.3}s {}",
                proof.debug_info()
            );
            let (family_proof_count, _, _) = proof.get_proof_counts();
            if unified_recursion_has_converged(self.prover.security(), family_proof_count) {
                break;
            }
            unified_recursion_layer += 1;
        }

        (proof, cycles)
    }
}
