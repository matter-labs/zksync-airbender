use crate::get_padded_binary;
use crate::unified_recursion_target_family_proofs;
use crate::unrolled::{
    flatten_proof_into_responses_for_unrolled_recursion, UnrolledProgramProof, UnrolledProgramSetup,
};
use crate::verifier_binaries;
use crate::{RecursionArtifact, RecursionLayer};
use gpu_prover::{
    circuit_type::{CircuitType, UnrolledCircuitType},
    execution::prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration},
    machine_type::MachineType,
};
use prover::merkle_trees::MerkleTreeCapVarLength;
use setups::{
    binary_u8_to_u32, get_unified_circuit_artifact_for_machine_type,
    get_unrolled_circuits_artifacts_for_machine_type, pad_bytecode_bytes_for_proving,
    pad_bytecode_for_proving, read_binary, CompiledCircuitsSet, CAP_SIZE, NUM_COSETS,
};
use verifier_common::prover::definitions::MerkleTreeCap;
use verifier_common::security_100::Security100Marker;
use verifier_common::security_80::Security80Marker;
use verifier_common::SecurityModel;

use crate::unified_circuit::flatten_proof_into_responses_for_unified_recursion;
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnrolledProverLevel {
    Base = 0,
    RecursionUnrolled = 1,
    RecursionUnified = 2,
}

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

    fn binary_setup_caps(
        &self,
        binary_key: usize,
    ) -> BTreeMap<UnrolledCircuitType, Vec<MerkleTreeCapVarLength>> {
        match self {
            Self::Security80(prover) => prover.binary_setup_caps(binary_key),
            Self::Security100(prover) => prover.binary_setup_caps(binary_key),
        }
    }

    fn common_setup_caps(&self, circuit_type: CircuitType) -> Vec<MerkleTreeCapVarLength> {
        match self {
            Self::Security80(prover) => prover.common_setup_caps(circuit_type),
            Self::Security100(prover) => prover.common_setup_caps(circuit_type),
        }
    }

    fn security(&self) -> SecurityModel {
        match self {
            Self::Security80(prover) => prover.security(),
            Self::Security100(prover) => prover.security(),
        }
    }
}

/// Assembles a program's [`UnrolledProgramSetup`] from the setup caps the GPU prover built
/// when the program was registered ([`ExecutionProver::binary_setup_caps`]) and when the
/// prover was constructed ([`ExecutionProver::common_setup_caps`] for the
/// inits-and-teardowns circuit). These are the same caps
/// `compute_setup_for_machine_configuration` derives, minus re-evaluating,
/// low-degree-extending and Merkle-committing every family's setup on the host — the
/// GPU prover already holds the setup traces and commits them on the device.
fn setup_from_gpu_caps(
    padded_binary: &[u8],
    circuit_caps: BTreeMap<UnrolledCircuitType, Vec<MerkleTreeCapVarLength>>,
    inits_and_teardowns_caps: Vec<MerkleTreeCapVarLength>,
) -> UnrolledProgramSetup {
    fn fixed_caps(
        circuit_type: UnrolledCircuitType,
        caps: Vec<MerkleTreeCapVarLength>,
    ) -> [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] {
        assert_eq!(
            caps.len(),
            NUM_COSETS,
            "{circuit_type:?}: expected one setup cap per coset"
        );
        caps.into_iter()
            .map(|cap| MerkleTreeCap {
                cap: cap.cap.try_into().unwrap_or_else(|cap: Vec<_>| {
                    panic!(
                        "{circuit_type:?}: setup cap holds {} digests, expected {CAP_SIZE}",
                        cap.len()
                    )
                }),
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    assert!(
        !circuit_caps.contains_key(&UnrolledCircuitType::InitsAndTeardowns),
        "inits-and-teardowns is not one of a binary's circuits"
    );
    let inits_and_teardowns_setup = fixed_caps(
        UnrolledCircuitType::InitsAndTeardowns,
        inits_and_teardowns_caps,
    );
    let mut circuit_families_setups: Vec<_> = circuit_caps
        .into_iter()
        .map(|(circuit_type, caps)| {
            (
                circuit_type.get_family_idx(),
                fixed_caps(circuit_type, caps),
            )
        })
        .collect();
    circuit_families_setups.sort_by_key(|(family_idx, _)| *family_idx);
    UnrolledProgramSetup::new_from_setups_and_binary(
        padded_binary,
        &circuit_families_setups,
        &inits_and_teardowns_setup,
    )
}

fn unified_recursion_has_converged(security: SecurityModel, family_proof_count: usize) -> bool {
    // Unified recursion converges once proof shape reaches target size.
    let target = unified_recursion_target_family_proofs(security);
    family_proof_count == target
}

impl UnrolledProver {
    /// A prover for the program in `{path_without_bin}.bin` and `{path_without_bin}.text`.
    pub fn new(
        security: SecurityModel,
        path_without_bin: &String,
        prover_configuration: ExecutionProverConfiguration,
        max_level: UnrolledProverLevel,
    ) -> Self {
        let (binary, _) = read_binary(Path::new(&format!("{path_without_bin}.bin")));
        let (text, _) = read_binary(Path::new(&format!("{path_without_bin}.text")));
        Self::from_program(security, &binary, &text, prover_configuration, max_level)
    }

    /// A prover for the program with this binary image and `.text` section.
    pub fn from_program(
        security: SecurityModel,
        binary: &[u8],
        text: &[u8],
        prover_configuration: ExecutionProverConfiguration,
        max_level: UnrolledProverLevel,
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
            let (binary, binary_u32) = (binary.to_vec(), binary_u8_to_u32(binary));
            let (text, text_u32) = (text.to_vec(), binary_u8_to_u32(text));
            prover.add_binary(
                UnrolledProverLevel::Base as usize,
                ExecutionKind::Unrolled,
                MachineType::FullUnsigned,
                binary_u32.clone(),
                text_u32.clone(),
                None,
            );
            info!("Assembling base layer setup from the GPU setup caps");
            let mut padded_binary = binary.clone();
            pad_bytecode_bytes_for_proving(&mut padded_binary);
            let mut padded_binary_u32 = binary_u32.clone();
            pad_bytecode_for_proving(&mut padded_binary_u32);
            // The GPU prover committed the base program's setup on the device while
            // registering it; take the caps from there instead of deriving the whole setup
            // a second time on the CPU (minutes for a production binary).
            let setup = setup_from_gpu_caps(
                &padded_binary,
                prover.binary_setup_caps(UnrolledProverLevel::Base as usize),
                prover.common_setup_caps(CircuitType::Unrolled(
                    UnrolledCircuitType::InitsAndTeardowns,
                )),
            );
            let compiled_layouts = get_unrolled_circuits_artifacts_for_machine_type::<
                IMStandardIsaConfigWithUnsignedMulDiv,
            >(&padded_binary_u32);
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
            info!("Loading recursion in unrolled layer setup");
            let mut padded_binary_u32 = binary_u32.clone();
            pad_bytecode_for_proving(&mut padded_binary_u32);
            // The embedded verifier's setup is a per-release constant; see
            // `verifier_binaries::recursion_setup`.
            let setup =
                verifier_binaries::recursion_setup(security, RecursionLayer::Unrolled).clone();
            let compiled_layouts = get_unrolled_circuits_artifacts_for_machine_type::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&padded_binary_u32);
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
            info!("Loading recursion in unified layer setup");
            let mut padded_binary_u32 = binary_u32.clone();
            pad_bytecode_for_proving(&mut padded_binary_u32);
            let setup =
                verifier_binaries::recursion_setup(security, RecursionLayer::Unified).clone();
            let compiled_layouts = get_unified_circuit_artifact_for_machine_type::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&padded_binary_u32);
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

/// The host-side state of a [`UnifiedRecursionProver`]: pinned host memory pools and
/// circuit precomputations, with the embedded unified-layer recursion program of the
/// given security model already registered.
///
/// Building this is the expensive part of constructing a [`UnifiedRecursionProver`]
/// (it page-locks tens of gigabytes of host memory and computes the unified circuit's
/// setup trace on the CPU) but holds no GPU resources. Build it once and derive a
/// prover per proving session via [`UnifiedRecursionProver::from_host_state`]: the
/// derived prover only creates the CUDA contexts and device memory pool, and dropping
/// it releases all device memory while this state stays warm.
pub struct UnifiedRecursionProverHostState {
    security: SecurityModel,
    state: gpu_prover::execution::prover::ExecutionProverHostState,
}

impl UnifiedRecursionProverHostState {
    pub fn new(
        security: SecurityModel,
        prover_configuration: ExecutionProverConfiguration,
    ) -> Self {
        let mut state =
            gpu_prover::execution::prover::ExecutionProverHostState::new(prover_configuration);
        let binary = verifier_binaries::recursion_artifact(
            security,
            RecursionLayer::Unified,
            RecursionArtifact::Bin,
        );
        let text = verifier_binaries::recursion_artifact(
            security,
            RecursionLayer::Unified,
            RecursionArtifact::Txt,
        );
        state.add_binary(
            UnifiedRecursionProver::BINARY_KEY,
            ExecutionKind::Unified,
            MachineType::Reduced,
            binary_u8_to_u32(binary),
            binary_u8_to_u32(text),
            None,
        );
        Self { security, state }
    }

    pub fn security(&self) -> SecurityModel {
        self.security
    }

    /// The page-locked host memory this state holds; see
    /// [`gpu_prover::execution::prover::ExecutionProverHostState::pinned_host_bytes`].
    pub fn pinned_host_bytes(&self) -> usize {
        self.state.pinned_host_bytes()
    }
}

/// GPU prover for the unified recursion layer only: proves caller-supplied
/// witness words with the embedded unified-layer recursion program.
///
/// The combined-recursion flow builds its witnesses on the host and only needs
/// the GPU for the unified proving passes, so unlike [`UnrolledProver`] no base
/// or unrolled level state is set up and no program files are read.
pub struct UnifiedRecursionProver {
    prover: RuntimeExecutionProver,
}

impl UnifiedRecursionProver {
    const BINARY_KEY: usize = 0;

    pub fn new(
        security: SecurityModel,
        prover_configuration: ExecutionProverConfiguration,
    ) -> Self {
        Self::from_host_state(&UnifiedRecursionProverHostState::new(
            security,
            prover_configuration,
        ))
    }

    /// Derives a prover from prebuilt host state, creating only the GPU-side
    /// resources (CUDA contexts and the device memory pool). Dropping the prover
    /// releases all of its device memory; the host state can be reused for the
    /// next proving session.
    pub fn from_host_state(host_state: &UnifiedRecursionProverHostState) -> Self {
        let prover =
            match host_state.security {
                SecurityModel::Security80 => {
                    RuntimeExecutionProver::Security80(
                        ExecutionProver::<Security80Marker>::with_host_state(&host_state.state),
                    )
                }
                SecurityModel::Security100 => RuntimeExecutionProver::Security100(
                    ExecutionProver::<Security100Marker>::with_host_state(&host_state.state),
                ),
            };
        Self { prover }
    }

    /// Prove one unified-layer pass over the given witness words. The caller is
    /// responsible for stamping the recursion chain onto the returned proof.
    pub fn prove(&self, batch_id: u64, witness: Vec<u32>) -> UnrolledProgramProof {
        let source = QuasiUARTSource::new_with_reads(witness);
        self.prover
            .commit_memory_and_prove(batch_id, Self::BINARY_KEY, source)
            .into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unrolled::compute_setup_for_machine_configuration;

    /// The base-layer setup assembled from the GPU prover's setup caps must be exactly
    /// what the CPU derivation yields: same caps, same end params, same exit PC and
    /// binary hash — it seeds the recursion chain every proof carries. Needs a CUDA
    /// device; the CPU side takes a few minutes.
    #[test]
    fn gpu_base_layer_setup_matches_the_cpu_derivation() {
        let path_without_bin = format!(
            "{}/../examples/hashed_fibonacci/app",
            env!("CARGO_MANIFEST_DIR")
        );
        let prover = UnrolledProver::new(
            SecurityModel::Security100,
            &path_without_bin,
            ExecutionProverConfiguration::default(),
            UnrolledProverLevel::Base,
        );
        let from_gpu = &prover.level_data[&UnrolledProverLevel::Base].setup;

        let (mut padded_binary, _) = read_binary(Path::new(&format!("{path_without_bin}.bin")));
        let (mut padded_text, _) = read_binary(Path::new(&format!("{path_without_bin}.text")));
        pad_bytecode_bytes_for_proving(&mut padded_binary);
        pad_bytecode_bytes_for_proving(&mut padded_text);
        let from_cpu = compute_setup_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&padded_binary, &padded_text);

        assert_eq!(from_gpu, &from_cpu);
    }
}
