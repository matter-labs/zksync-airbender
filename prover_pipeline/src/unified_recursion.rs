use execution_prover_model::circuit_type::{DelegationCircuitType, UnrolledCircuitType};
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use std::collections::BTreeMap;
use std::fmt;
use verifier_common::fsv_binaries::BlakeMode;

#[derive(Debug, PartialEq, Eq)]
pub(super) struct UnifiedProofShape {
    pub(super) riscv: BTreeMap<u32, usize>,
    pub(super) delegations: BTreeMap<u32, usize>,
}

impl UnifiedProofShape {
    pub(super) fn from_proof(proof: &ProgramProof) -> Self {
        Self {
            riscv: proof
                .riscv_proofs
                .iter()
                .map(|(&family, proofs)| (family, proofs.len()))
                .collect(),
            delegations: proof
                .delegation_proofs
                .iter()
                .map(|(&kind, proofs)| (kind, proofs.len()))
                .collect(),
        }
    }

    /// Match execution_prover's trace producer: both unified cycles and
    /// delegation calls use the full circuit domain, with no reserved row.
    /// `unified` selects the unified circuit geometry the cycles are chunked
    /// into (2^23 for regular recursion, 2^22 for the feeder layers).
    pub(super) fn from_counters(
        unified: UnrolledCircuitType,
        counters: &DelegationsAndUnifiedCounters,
    ) -> Self {
        assert!(
            matches!(
                unified,
                UnrolledCircuitType::Unified | UnrolledCircuitType::Unified22
            ),
            "{unified:?} is not a unified circuit"
        );
        let riscv = [(
            unified.get_family_idx() as u32,
            counters.cycles.div_ceil(unified.get_domain_size()),
        )]
        .into_iter()
        .filter(|(_, count)| *count != 0)
        .collect();
        let delegations = [
            (
                DelegationCircuitType::Blake2WithCompression,
                counters.blake_calls,
            ),
            (
                DelegationCircuitType::Blake2GFunction,
                counters.blake_g_function_calls,
            ),
            (
                DelegationCircuitType::BigIntWithControl,
                counters.bigint_calls,
            ),
            (DelegationCircuitType::KeccakSpecial5, counters.keccak_calls),
        ]
        .into_iter()
        .filter(|(_, calls)| *calls != 0)
        .map(|(circuit, calls)| {
            (
                circuit.get_delegation_type_id() as u32,
                calls.div_ceil(circuit.get_domain_size()),
            )
        })
        .collect();
        Self { riscv, delegations }
    }

    pub(super) fn has_converged(&self, final_mode: BlakeMode) -> bool {
        let riscv: usize = self.riscv.values().sum();
        let delegation: usize = self.delegations.values().sum();
        let expected_delegations = usize::from(final_mode != BlakeMode::BlakeSpecialOpcodes);
        riscv == 1 && delegation == expected_delegations
    }
}

impl fmt::Display for UnifiedProofShape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "riscv={:?}, delegations={:?}",
            self.riscv, self.delegations
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(riscv: &[(u32, usize)], delegations: &[(u32, usize)]) -> UnifiedProofShape {
        UnifiedProofShape {
            riscv: riscv.iter().copied().collect(),
            delegations: delegations.iter().copied().collect(),
        }
    }

    #[test]
    fn unified_predictions_round_up_at_full_domain_boundaries() {
        for circuit in [UnrolledCircuitType::Unified, UnrolledCircuitType::Unified22] {
            unified_predictions_round_up_at_full_domain_boundaries_for(circuit);
        }
    }

    fn unified_predictions_round_up_at_full_domain_boundaries_for(circuit: UnrolledCircuitType) {
        let capacity = circuit.get_domain_size();
        for (cycles, chunks) in [(0, 0), (capacity, 1), (capacity + 1, 2)] {
            let predicted = UnifiedProofShape::from_counters(
                circuit,
                &DelegationsAndUnifiedCounters {
                    cycles,
                    ..Default::default()
                },
            );
            assert_eq!(
                predicted
                    .riscv
                    .get(&(circuit.get_family_idx() as u32))
                    .copied()
                    .unwrap_or(0),
                chunks
            );
            assert!(predicted.delegations.is_empty());
        }
    }

    #[test]
    fn each_delegation_uses_its_own_counter_and_full_domain_capacity() {
        for &circuit in DelegationCircuitType::get_all_delegation_types() {
            let capacity = circuit.get_domain_size();
            for (calls, chunks) in [(0, 0), (capacity, 1), (capacity + 1, 2)] {
                let mut counters = DelegationsAndUnifiedCounters::default();
                match circuit {
                    DelegationCircuitType::Blake2WithCompression => counters.blake_calls = calls,
                    DelegationCircuitType::Blake2GFunction => {
                        counters.blake_g_function_calls = calls
                    }
                    DelegationCircuitType::BigIntWithControl => counters.bigint_calls = calls,
                    DelegationCircuitType::KeccakSpecial5 => counters.keccak_calls = calls,
                    DelegationCircuitType::KeccakColumnParity
                    | DelegationCircuitType::KeccakThetaRho
                    | DelegationCircuitType::KeccakChi5 => continue,
                }
                let predicted =
                    UnifiedProofShape::from_counters(UnrolledCircuitType::Unified, &counters);
                let expected = if chunks == 0 {
                    shape(&[], &[])
                } else {
                    shape(&[], &[(circuit.get_delegation_type_id() as u32, chunks)])
                };
                assert_eq!(predicted, expected);
            }
        }
    }

    #[test]
    fn convergence_is_one_unified_chunk_plus_the_mode_delegations() {
        assert!(shape(&[(128, 1)], &[(7, 1)]).has_converged(BlakeMode::Compression));
    }
}
