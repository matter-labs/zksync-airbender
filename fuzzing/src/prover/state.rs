use std::cell::RefCell;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use crate::prover::circuits::CircuitRegistry;
use crate::prover::crashes::BugReport;
use crate::prover::crashes::CrashArtifact;
use crate::prover::seeds::expand_seed_cases;
use crate::prover::seeds::CacheEntry;
use crate::prover::seeds::SeedCase;
use crate::prover::seeds::SeedProgram;
use crate::prover::FuzzerConfig;

#[derive(Default, Debug)]
struct CrashId {
    id: RefCell<u64>,
}

impl CrashId {
    fn new(id: u64) -> Self {
        Self {
            id: RefCell::new(id),
        }
    }

    fn next(&self) -> u64 {
        let id = *self.id.borrow();
        {
            *self.id.borrow_mut() += 1;
        }
        id
    }
}

/// In-memory state accumulated across a fuzzing run.
#[derive(Debug, Default)]
pub struct FuzzerState {
    /// Flattened per-circuit seed cases derived from the cache.
    seed_cases: Vec<SeedCase>,
    /// Next crash id to allocate when persisting a bug report.
    next_crash_id: CrashId,
}

impl FuzzerState {
    /// Builds the initial in-memory fuzzer state from the configured corpus and output dirs.
    pub fn new(config: &FuzzerConfig, registry: &CircuitRegistry) -> io::Result<Self> {
        let cache_entries = SeedProgram::find_programs(&config.input_dir)?
            .into_iter()
            .map(|program| CacheEntry::load_or_create(program, registry, &config.cache_dir))
            .collect::<Result<Vec<_>, _>>()?;
        let seed_cases = expand_seed_cases(cache_entries);
        let next_crash_id = CrashId::new(discover_next_crash_id(&config.crash_dir)?);

        Ok(Self {
            seed_cases,
            next_crash_id,
        })
    }

    /// Allocates a new crash id, persists the corresponding artifact, and returns its path.
    pub fn save_bug(&self, report: BugReport, crash_dir: &Path) -> io::Result<PathBuf> {
        let crash_id = self.next_crash_id.next();

        let artifact = CrashArtifact::new(crash_id, report);
        let path = crash_dir.join(artifact.file_name());
        artifact.write(&path)?;

        Ok(path)
    }

    pub fn seed_cases(&self) -> &[SeedCase] {
        &self.seed_cases
    }

    pub fn seed_cases_mut(&mut self) -> &mut Vec<SeedCase> {
        &mut self.seed_cases
    }
}

fn discover_next_crash_id(crash_dir: &Path) -> io::Result<u64> {
    let mut max_seen = None;

    for entry in std::fs::read_dir(crash_dir)? {
        let entry = entry?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };

        if let Some(raw_id) = name
            .strip_prefix("id:")
            .and_then(|rest| rest.split(',').next())
        {
            if let Ok(id) = raw_id.parse::<u64>() {
                max_seen = Some(max_seen.map_or(id, |current: u64| current.max(id)));
            }
        }
    }

    Ok(max_seen.map_or(0, |id| id + 1))
}
