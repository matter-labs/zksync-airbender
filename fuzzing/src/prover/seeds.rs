use std::cell::OnceCell;
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use prover::risc_v_simulator::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use prover::worker::Worker;
use sha2::Digest;
use sha2::Sha256;

use crate::prover::circuits::CircuitKind;
use crate::prover::circuits::CircuitRegistry;
use crate::rv32im::binary::Binary;
use crate::rv32im::prover::circuits::ProofInputs;
use crate::rv32im::prover::prepare_execution;
use crate::rv32im::prover::DEFAULT_WORKERS;
use crate::rv32im::VM;
use crate::utils::env_conf;
use crate::utils::mute;

#[derive(Debug)]
pub struct SeedProgram {
    name: String,
    binary_path: PathBuf,
    text_path: PathBuf,
    binary_bytes: OnceCell<Vec<u8>>,
    text_bytes: OnceCell<Vec<u8>>,
    hash: OnceCell<String>,
}

impl SeedProgram {
    pub fn new(name: String, binary_path: PathBuf, text_path: PathBuf) -> Self {
        Self {
            name,
            binary_path,
            text_path,
            binary_bytes: OnceCell::new(),
            text_bytes: OnceCell::new(),
            hash: OnceCell::new(),
        }
    }

    pub fn find_programs(input_dir: &Path) -> io::Result<Vec<SeedProgram>> {
        let mut bin_paths = BTreeMap::<String, PathBuf>::new();
        let mut text_paths = BTreeMap::<String, PathBuf>::new();

        for entry in fs::read_dir(input_dir)? {
            let entry = entry?;
            let path = entry.path();

            if !entry.file_type()?.is_file() {
                continue;
            }

            match path.extension().and_then(OsStr::to_str) {
                Some("bin") => {
                    if let Some(stem) = file_stem_string(&path) {
                        bin_paths.insert(stem, path);
                    }
                }
                Some("text") => {
                    if let Some(stem) = file_stem_string(&path) {
                        text_paths.insert(stem, path);
                    }
                }
                _ => {}
            }
        }

        let mut programs = Vec::with_capacity(bin_paths.len());
        for (name, bin_path) in bin_paths {
            let text_path = text_paths.remove(&name).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("missing .text file for seed program `{name}`"),
                )
            })?;

            programs.push(SeedProgram::new(name, bin_path, text_path));
        }

        Ok(programs)
    }

    pub fn binary(&self) -> io::Result<Binary<'_>> {
        Ok(Binary::new(self.binary_bytes()?, Some(self.text_bytes()?)))
    }

    pub fn cache_file_name(&self) -> io::Result<String> {
        Ok(format!("{}-{}.data", self.name, self.hash()?))
    }

    fn hash(&self) -> io::Result<&str> {
        if let Some(hash) = self.hash.get() {
            return Ok(hash);
        }

        let hash = short_program_hash(self.binary_bytes()?, self.text_bytes()?);
        let _ = self.hash.set(hash);
        Ok(self.hash.get().expect("content hash initialized"))
    }

    fn binary_bytes(&self) -> io::Result<&[u8]> {
        if let Some(bytes) = self.binary_bytes.get() {
            return Ok(bytes);
        }

        let bytes = fs::read(&self.binary_path)?;
        let _ = self.binary_bytes.set(bytes);
        Ok(self.binary_bytes.get().expect("binary bytes initialized"))
    }

    fn text_bytes(&self) -> io::Result<&[u8]> {
        if let Some(bytes) = self.text_bytes.get() {
            return Ok(bytes);
        }

        let bytes = fs::read(&self.text_path)?;
        let _ = self.text_bytes.set(bytes);
        Ok(self.text_bytes.get().expect("text bytes initialized"))
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CacheEntry {
    pub seed: String,
    pub inputs: Vec<StoredProofInputs>,
}

impl CacheEntry {
    pub fn load_or_create(
        program: SeedProgram,
        registry: &CircuitRegistry,
        cache_dir: &Path,
    ) -> io::Result<Self> {
        let path = cache_dir.join(program.cache_file_name()?);
        let entry = if path.exists() {
            Self::load(&path)?
        } else {
            let entry = Self::create(program, registry)?;
            entry.write(&path)?;
            entry
        };

        Ok(entry)
    }

    fn create(program: SeedProgram, registry: &CircuitRegistry) -> io::Result<Self> {
        let Ok(result) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            log::info!("Executing seed program {}", program.name);
            let binary = program.binary()?;
            let vm = mute(|| {
                let mut vm = VM::new(&binary);
                vm.run();
                vm
            });
            log::debug!("VM finished execution");
            let worker = Worker::new_with_num_threads(env_conf("PROVER_WORKERS", DEFAULT_WORKERS));
            let snapshot = vm.snapshot();
            log::debug!("Collecting common circuit data");
            let prepared = mute(|| prepare_execution(snapshot, &worker));
            Ok(Self {
                seed: program.name.clone(),
                inputs: registry
                    .circuits()
                    .iter()
                    .map(|kind| {
                        log::debug!("Generating inputs for circuit {kind}");
                        mute(|| registry.generate_inputs(*kind, snapshot, &prepared))
                    })
                    .collect(),
            })
        })) else {
            return Err(io::Error::other(format!(
                "Preparations for seed program {} failed",
                program.name
            )));
        };

        result
    }

    pub(crate) fn load(path: &Path) -> io::Result<Self> {
        let contents = fs::read(path)?;
        serde_json::from_slice(&contents).map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "failed to deserialize cache entry `{}`: {err}",
                    path.display()
                ),
            )
        })
    }

    fn write(&self, path: &Path) -> io::Result<()> {
        let payload = serde_json::to_vec_pretty(self).map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "failed to serialize cache entry `{}`: {err}",
                    path.display()
                ),
            )
        })?;
        fs::write(path, payload)
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SeedCase {
    pub seed_program: String,
    pub circuit: CircuitKind,
    pub base_input: StoredProofInputs,
}

impl std::fmt::Display for SeedCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.seed_program,
            match self.circuit {
                CircuitKind::AddSubLuiAuipcMop => "ADD/SUB/LUI/AUIPC/MOP",
                CircuitKind::JumpBranchSlt => "JUMP/BRANCH/SLT",
                CircuitKind::XorAndOrShiftCsr => "XOR/AND/OR/SHIFT/CSR",
                CircuitKind::MulDiv => "MUL/DIV",
                CircuitKind::LoadStore => "word LOAD/STORE",
                CircuitKind::SubwordLoadStore => "subword LOAD/STORE",
                CircuitKind::InitsAndTeardowns => todo!(),
                CircuitKind::BlakeDelegation => todo!(),
                CircuitKind::KeccakDelegation => todo!(),
            }
        )
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, PartialEq)]
pub enum StoredProofInputs {
    AddSubLuiAuipcMop(ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>),
    JumpBranchSlt(ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>),
    XorAndOrShiftCsr(ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>),
    MulDiv(ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>),
    LoadStore(ProofInputs<MemoryOpcodeTracingDataWithTimestamp>, Vec<u32>),
    SubwordLoadStore(ProofInputs<MemoryOpcodeTracingDataWithTimestamp>, Vec<u32>),
    InitsAndTeardowns(()),
    BlakeDelegation(()),
    KeccakDelegation(()),
}

impl StoredProofInputs {
    pub fn circuit(&self) -> CircuitKind {
        match self {
            Self::JumpBranchSlt(inputs)
            | Self::MulDiv(inputs)
            | Self::XorAndOrShiftCsr(inputs)
            | Self::AddSubLuiAuipcMop(inputs) => CircuitKind::from_family_idx(inputs.family_idx())
                .expect("stored proof inputs contain an unsupported circuit family idx"),
            Self::SubwordLoadStore(inputs, _) | Self::LoadStore(inputs, _) => {
                CircuitKind::from_family_idx(inputs.family_idx())
                    .expect("stored proof inputs contain an unsupported circuit family idx")
            }
            Self::InitsAndTeardowns(_) => CircuitKind::InitsAndTeardowns,
            Self::BlakeDelegation(_) => CircuitKind::BlakeDelegation,
            Self::KeccakDelegation(_) => CircuitKind::KeccakDelegation,
        }
    }
}

pub(crate) fn load_seed_case_from_cache(
    cache_dir: &Path,
    seed_program: &str,
    circuit: CircuitKind,
) -> io::Result<SeedCase> {
    for entry in fs::read_dir(cache_dir)? {
        let entry = entry?;
        if !entry.file_type()?.is_file() {
            continue;
        }

        let cache_entry = CacheEntry::load(&entry.path())?;
        if cache_entry.seed != seed_program {
            continue;
        }

        if let Some(base_input) = cache_entry
            .inputs
            .into_iter()
            .find(|input| input.circuit() == circuit)
        {
            return Ok(SeedCase {
                seed_program: seed_program.to_owned(),
                circuit,
                base_input,
            });
        }
    }

    Err(io::Error::new(
        io::ErrorKind::NotFound,
        format!(
            "no cached seed case found for seed `{seed_program}` and circuit `{}`",
            circuit.slug()
        ),
    ))
}

pub fn expand_seed_cases(entries: impl IntoIterator<Item = CacheEntry>) -> Vec<SeedCase> {
    entries
        .into_iter()
        .flat_map(|entry| {
            entry.inputs.into_iter().map(move |base_input| SeedCase {
                seed_program: entry.seed.clone(),
                circuit: base_input.circuit(),
                base_input,
            })
        })
        .collect()
}

fn file_stem_string(path: &Path) -> Option<String> {
    path.file_stem()
        .and_then(OsStr::to_str)
        .map(ToOwned::to_owned)
}

fn short_program_hash(bin_bytes: &[u8], text_bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bin_bytes);
    hasher.update(text_bytes);
    let digest = hasher.finalize();
    digest[..4]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
