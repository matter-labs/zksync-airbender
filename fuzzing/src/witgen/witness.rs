use std::ops::Index;

use prover::cs::cs::circuit::Circuit as _;
use prover::cs::cs::circuit::CircuitOutput;
use prover::cs::cs::cs_reference::BasicAssembly;
use prover::cs::cs::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use prover::cs::definitions::Variable;
use prover::field::PrimeField;
use rand::rngs::SmallRng;
use rand::Rng as _;

use crate::witgen::oracles::rand::RngOracle;
use crate::witgen::oracles::rand::RngOracleConfig;
use crate::witgen::targets::FuzzTarget;
use crate::witgen::validator::check_constraints;

/// Maps the n-th variable to its value.
pub struct Assignment<F> {
    values: Vec<F>,
}

impl<F> FromIterator<F> for Assignment<F> {
    fn from_iter<T: IntoIterator<Item = F>>(iter: T) -> Self {
        Self {
            values: iter.into_iter().collect(),
        }
    }
}

impl<F> Index<Variable> for Assignment<F> {
    type Output = F;

    fn index(&self, index: Variable) -> &Self::Output {
        &self.values[index.0 as usize]
    }
}

impl<F> Index<&Variable> for Assignment<F> {
    type Output = F;

    fn index(&self, index: &Variable) -> &Self::Output {
        &self.values[index.0 as usize]
    }
}

impl<F: std::fmt::Debug> std::fmt::Debug for Assignment<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ ")?;
        let count = self.values.len();
        self.values.iter().enumerate().try_for_each(|(n, value)| {
            write!(f, "v{n} ↦ {value:?}")?;
            // Interleave a comma between the entries.
            if n + 1 < count {
                write!(f, ", ")
            } else {
                Ok(())
            }
        })?;
        write!(f, "}} ")
    }
}

#[derive(Debug)]
pub struct Witness<F: PrimeField> {
    /// Maps the n-th variable to its value. If the value was not available defaults it to 0.
    pub variables: Assignment<F>,
    /// Result of circuit synthesis.
    pub circuit_output: CircuitOutput<F>,
}

impl<F: PrimeField> Witness<F> {
    /// Collects a witness that satisfies the constraints of the circuit.
    ///
    /// Returns the satisfying assignment along with the circuit output.
    /// If the circuit fails, returns `None`.
    pub fn collect(target: &dyn FuzzTarget<F>) -> Option<Self> {
        let (circuit_output, wit_placer) = std::panic::catch_unwind(|| {
            let mut cs = BasicAssembly::<F>::new();
            cs.witness_placer = Some(populate_inputs(target));
            target.synthesize(&mut cs);
            cs.finalize()
        })
        .ok()?;

        let Some(wit_placer) = wit_placer else {
            unreachable!();
        };

        let variables = (0..circuit_output.num_of_variables as u64)
            .map(Variable)
            .map(|v| wit_placer.get_value(v).unwrap_or(F::ZERO))
            .collect();
        Some(Self {
            variables,
            circuit_output,
        })
    }

    /// Returns true if the assignment satisfies the constraints defined in the circuit output.
    pub fn satisfies_constraints(&self) -> bool {
        check_constraints(
            &self.circuit_output.constraints,
            std::slice::from_ref(&self.variables),
        )
    }
}

const MAX_TABLE_LEN: u32 = 100;

/// Populates the inputs used by the witness placer.
fn populate_inputs<F: PrimeField>(target: &dyn FuzzTarget<F>) -> CSDebugWitnessEvaluator<F> {
    let mut rng: SmallRng = rand::make_rng();
    let table_len = rng.next_u32() % MAX_TABLE_LEN;

    let preprocessed_decoder_table: Vec<_> = (0..table_len)
        .map(|_| target.random_decoder_data(&mut rng))
        .collect();
    CSDebugWitnessEvaluator::new_with_oracle_and_preprocessed_decoder(
        RngOracle::new(
            rng,
            RngOracleConfig {
                pc_mod: preprocessed_decoder_table.len() as u32,
            },
        ),
        preprocessed_decoder_table,
    )
}
