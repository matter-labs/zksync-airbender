use std::fmt;

use crate::forward::artifact::validate_forward_artifact;
use crate::forward::search::producer;
use crate::{compile_forward, ForwardArtifactError, ForwardSearchArtifact};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SearchConfig {
    pub population: usize,
    pub evaluations: usize,
    pub tournament: usize,
    pub elitism: usize,
    pub crossover_rate: f64,
    pub mutation_rate: f64,
    pub mutation_sigma: f64,
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
            && self.mutation_sigma > 0.0;
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
    pub cache_buckets: usize,
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
        if incumbent.budget_buckets != request.cache_buckets {
            return Err(ForwardSearchError::IncumbentMismatch(format!(
                "incumbent budget {} does not match {}",
                incumbent.budget_buckets, request.cache_buckets
            )));
        }
        validate_forward_artifact(request.dag, incumbent).map_err(ForwardSearchError::Artifact)?;
    }
    request.config.validate()?;

    let mut artifact = producer::produce_circuit_schedule(
        request.dag,
        request.cache_buckets,
        &request.config,
        request.seed,
        request.incumbent,
    );
    artifact.circuit = request.circuit.to_owned();
    compile_forward(request.dag, &artifact).map_err(ForwardSearchError::Compile)?;
    Ok(artifact)
}
