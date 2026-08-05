use std::fmt;

use crate::forward::search::{producer, search as engine};
use crate::{
    ForwardArtifactError, ForwardResourceProfile, ForwardSearchArtifact, compile_forward,
    validate_forward_artifact,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrossoverKind {
    Blx,
    Order,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SearchConfig {
    pub population: usize,
    pub evaluations: usize,
    pub tournament: usize,
    pub elitism: usize,
    pub crossover_rate: f64,
    pub mutation_rate: f64,
    pub mutation_sigma: f64,
    pub local_steps: usize,
    pub local_elite: usize,
    pub crossover: CrossoverKind,
}

impl SearchConfig {
    pub const fn production() -> Self {
        Self {
            population: 64,
            evaluations: 20_000,
            tournament: 3,
            elitism: 2,
            crossover_rate: 0.9,
            mutation_rate: 0.1,
            mutation_sigma: 0.15,
            local_steps: 2,
            local_elite: 0,
            crossover: CrossoverKind::Order,
        }
    }

    fn validate(self) -> Result<(), ForwardSearchError> {
        let valid = self.population > 0
            && self.evaluations >= self.population
            && self.tournament > 0
            && self.elitism < self.population
            && (0.0..=1.0).contains(&self.crossover_rate)
            && (0.0..=1.0).contains(&self.mutation_rate)
            && self.mutation_sigma.is_finite()
            && self.mutation_sigma > 0.0
            && self.local_elite <= self.population;
        if valid {
            Ok(())
        } else {
            Err(ForwardSearchError::InvalidConfig)
        }
    }
}

pub struct ForwardSearchRequest<'a> {
    pub circuit: &'a str,
    pub dag: &'a gkr_eval_ir::DagCircuit,
    pub resources: ForwardResourceProfile,
    pub config: SearchConfig,
    pub seed: u64,
    pub incumbent: Option<&'a ForwardSearchArtifact>,
}

#[derive(Debug)]
pub enum ForwardSearchError {
    Artifact(ForwardArtifactError),
    InvalidConfig,
    IncumbentMismatch(String),
    Compile(crate::ForwardCompileError),
}

impl fmt::Display for ForwardSearchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Artifact(error) => write!(f, "{error}"),
            Self::InvalidConfig => f.write_str("invalid forward search configuration"),
            Self::IncumbentMismatch(message) => f.write_str(message),
            Self::Compile(error) => write!(f, "forward compile failed: {error:?}"),
        }
    }
}

impl std::error::Error for ForwardSearchError {}

pub fn search_forward(
    request: ForwardSearchRequest<'_>,
) -> Result<ForwardSearchArtifact, ForwardSearchError> {
    if let Some(incumbent) = request.incumbent {
        if incumbent.circuit != request.circuit {
            return Err(ForwardSearchError::IncumbentMismatch(format!(
                "incumbent circuit {:?} does not match {:?}",
                incumbent.circuit, request.circuit
            )));
        }
        if incumbent.budget != request.resources.cache_cells {
            return Err(ForwardSearchError::IncumbentMismatch(format!(
                "incumbent budget {} does not match {}",
                incumbent.budget, request.resources.cache_cells
            )));
        }
        validate_forward_artifact(request.dag, incumbent).map_err(ForwardSearchError::Artifact)?;
    }
    request.config.validate()?;

    let config = engine::SearchConfig {
        pop: request.config.population,
        evals: request.config.evaluations,
        seed: request.seed,
        tournament: request.config.tournament,
        elitism: request.config.elitism,
        crossover_rate: request.config.crossover_rate,
        mutation_rate: request.config.mutation_rate,
        mutation_sigma: request.config.mutation_sigma,
        local_steps: request.config.local_steps,
        local_elite: request.config.local_elite,
        crossover_kind: match request.config.crossover {
            CrossoverKind::Blx => engine::CrossoverKind::Blx,
            CrossoverKind::Order => engine::CrossoverKind::Order,
        },
    };
    let mut artifact = producer::produce_circuit_schedule(
        request.dag,
        request.resources.cache_cells,
        &config,
        request.incumbent,
    );
    artifact.circuit = request.circuit.to_owned();
    validate_forward_artifact(request.dag, &artifact).map_err(ForwardSearchError::Artifact)?;
    compile_forward(request.dag, &artifact).map_err(ForwardSearchError::Compile)?;
    Ok(artifact)
}
