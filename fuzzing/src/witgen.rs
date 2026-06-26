use prover::cs::cs::circuit::CircuitOutput;
use prover::field::Mersenne31Field as F;

use crate::witgen::checks::Check;
use crate::witgen::checks::Checks;
use crate::witgen::targets::Circuits;
use crate::witgen::targets::FuzzTarget;
use crate::witgen::witness::Assignment;
use crate::witgen::witness::Witness;

pub mod checks;
mod oracles;
pub mod targets;
mod validator;
mod witness;

/// Entrypoint function for the witgen fuzzer.
pub fn run(target: Circuits, check: Checks, sample_size: usize) {
    run_fuzzer(
        target.instantiate().as_ref(),
        check.instantiate().as_ref(),
        sample_size,
    )
}

fn enumerated<K, V>(i: impl IntoIterator<Item = (K, V)>) -> impl Iterator<Item = (usize, K, V)> {
    i.into_iter().enumerate().map(|(n, (k, v))| (n, k, v))
}

/// Main loop called by the corresponding target entrypoint function.
fn run_fuzzer(target: &dyn FuzzTarget<F>, check: &dyn Check<F>, sample_size: usize) {
    log::info!("Running with target '{}'", target.name());
    log::info!("Requested {sample_size} samples...");
    let witnesses = collect_witnesses(target, sample_size);
    assert_eq!(witnesses.len(), sample_size);
    let aggregated = aggregate_witnesses(witnesses);
    log::info!(
        "The samples produced {} unique constraint systems",
        aggregated.len()
    );
    for (n, circuit, assignments) in enumerated(aggregated) {
        log::debug!("Checking constraint system #{n}...");
        match check.check(circuit, &assignments) {
            Ok(_) => log::debug!("Check passed!"),
            Err(reason) => log::error!("Constraint system #{n} failed check: {reason}"),
        }
    }
}

/// Collects `n` witnesses that satisfy the constraints of the circuit.
fn collect_witnesses(target: &dyn FuzzTarget<F>, n: usize) -> Vec<Witness<F>> {
    // Infinite iterator that will generate witnesses with random inputs.
    std::iter::repeat_with(|| Witness::collect(target))
        // Since we have `Option<Witness<F>>` we can flatten to get rid of the failing ones.
        .flatten()
        // Double check that the witness satisfy the constraints.
        .filter(Witness::satisfies_constraints)
        // We take `n` and collect.
        .take(n)
        // Collect into the array.
        .collect()
}

type Entry = (CircuitOutput<F>, Vec<Assignment<F>>);

/// Groups the witnesses by their circuit output.
///
/// We use an associative list because it's not easy to implement `std::hash::Hash` on
/// `CircuitOutput`.
fn aggregate_witnesses(witnesses: impl IntoIterator<Item = Witness<F>>) -> Vec<Entry> {
    let mut aggregated: Vec<Entry> = vec![];

    for witness in witnesses {
        let entry = aggregated.iter_mut().find_map(|(output, assignments)| {
            (*output == witness.circuit_output).then_some(assignments)
        });
        match entry {
            Some(assignments) => assignments.push(witness.variables),
            None => aggregated.push((witness.circuit_output, vec![witness.variables])),
        }
    }

    aggregated
}
