use execution_prover_model::circuit_type::{DelegationCircuitType, UnrolledCircuitType};
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use std::collections::BTreeMap;
use std::fmt;
use verifier_common::fsv_binaries::BlakeMode;

#[derive(Debug, PartialEq, Eq)]
pub(super) struct UnifiedProofShape {
    riscv: BTreeMap<u32, usize>,
    delegations: BTreeMap<u32, usize>,
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
    pub(super) fn from_counters(counters: &DelegationsAndUnifiedCounters) -> Self {
        let unified = UnrolledCircuitType::Unified;
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

    fn is_strictly_smaller_than(&self, current: &Self) -> bool {
        let components = [
            (&self.riscv, &current.riscv),
            (&self.delegations, &current.delegations),
        ];
        let none_grow = components.iter().all(|(next, current)| {
            next.iter()
                .all(|(kind, count)| count <= current.get(kind).unwrap_or(&0))
        });
        let some_shrink = components.iter().any(|(next, current)| {
            current
                .iter()
                .any(|(kind, count)| next.get(kind).unwrap_or(&0) < count)
        });
        none_grow && some_shrink
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

/// Decide whether to stop or prove another round at the same final geometry.
/// A terminal proof wins; otherwise every component must be nonincreasing and
/// at least one must shrink. Apply even after round one: the prediction runs
/// the final program over a final proof, not over the bridge proof.
pub(super) fn unified_recursion_step(
    round: usize,
    current: &UnifiedProofShape,
    predicted: &UnifiedProofShape,
    final_mode: BlakeMode,
) -> Result<bool, String> {
    if current.has_converged(final_mode) {
        return Ok(true);
    }
    if !predicted.is_strictly_smaller_than(current) {
        return Err(format!(
            "unified recursion is not compressing: round {round} produced {current}; next round predicts {predicted}"
        ));
    }
    Ok(false)
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
        let circuit = UnrolledCircuitType::Unified;
        let capacity = circuit.get_domain_size();
        for (cycles, chunks) in [
            (0, 0),
            (1, 1),
            (capacity - 1, 1),
            (capacity, 1),
            (capacity + 1, 2),
        ] {
            let predicted = UnifiedProofShape::from_counters(&DelegationsAndUnifiedCounters {
                cycles,
                ..Default::default()
            });
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
            for (calls, chunks) in [
                (0, 0),
                (1, 1),
                (capacity - 1, 1),
                (capacity, 1),
                (capacity + 1, 2),
            ] {
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
                let predicted = UnifiedProofShape::from_counters(&counters);
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
    fn reference_verifier_counts_predict_the_expected_shapes() {
        // Counts observed for the same recursion-unified checkpoint with the
        // compression and special-opcodes final verifiers, respectively.
        let compression = UnifiedProofShape::from_counters(&DelegationsAndUnifiedCounters {
            cycles: 4_137_327,
            blake_calls: 166_215,
            ..Default::default()
        });
        let blake_id = DelegationCircuitType::Blake2WithCompression.get_delegation_type_id() as u32;
        assert_eq!(compression, shape(&[(128, 1)], &[(blake_id, 1)]));
        let special = UnifiedProofShape::from_counters(&DelegationsAndUnifiedCounters {
            cycles: 19_146_961,
            ..Default::default()
        });
        assert_eq!(special, shape(&[(128, 3)], &[]));
        assert!(
            unified_recursion_step(1, &special, &special, BlakeMode::BlakeSpecialOpcodes).is_err()
        );
    }

    #[test]
    fn converges_in_the_first_final_round_without_requiring_a_smaller_prediction() {
        let larger = shape(&[(128, 3)], &[(7, 2)]);
        for mode in [BlakeMode::Compression, BlakeMode::BlakeSpecialOpcodes] {
            let current = if mode == BlakeMode::BlakeSpecialOpcodes {
                shape(&[(128, 1)], &[])
            } else {
                shape(&[(128, 1)], &[(7, 1)])
            };
            assert_eq!(unified_recursion_step(1, &current, &larger, mode), Ok(true));
        }
    }

    #[test]
    fn compresses_then_converges() {
        let first = shape(&[(128, 4)], &[(7, 2)]);
        let second = shape(&[(128, 2)], &[(7, 1)]);
        let third = shape(&[(128, 1)], &[(7, 1)]);
        assert_eq!(
            unified_recursion_step(1, &first, &second, BlakeMode::Compression),
            Ok(false)
        );
        assert_eq!(
            unified_recursion_step(2, &second, &third, BlakeMode::Compression),
            Ok(false)
        );
        assert_eq!(
            unified_recursion_step(3, &third, &third, BlakeMode::Compression),
            Ok(true)
        );
    }

    #[test]
    fn repeated_special_opcode_shape_is_rejected_after_the_first_final_round() {
        let current = shape(&[(128, 3)], &[]);
        let predicted = shape(&[(128, 3)], &[]);
        assert_eq!(unified_recursion_step(1, &current, &predicted, BlakeMode::BlakeSpecialOpcodes),
            Err("unified recursion is not compressing: round 1 produced riscv={128: 3}, delegations={}; next round predicts riscv={128: 3}, delegations={}".into()));
    }

    #[test]
    fn predicted_growth_is_rejected() {
        let current = shape(&[(128, 3)], &[(7, 1)]);
        for predicted in [shape(&[(128, 4)], &[(7, 1)]), shape(&[(128, 3)], &[(7, 2)])] {
            let error = unified_recursion_step(1, &current, &predicted, BlakeMode::Compression)
                .unwrap_err();
            assert!(error.starts_with("unified recursion is not compressing: round 1 produced "));
            assert!(error.contains("; next round predicts "));
        }
    }

    #[test]
    fn shrinking_one_component_does_not_offset_growth_elsewhere() {
        let current = shape(&[(128, 4)], &[(7, 3)]);
        for predicted in [
            shape(&[(128, 2), (129, 1)], &[(7, 1)]),
            shape(&[(128, 2)], &[(8, 1)]),
            shape(&[(128, 2)], &[(7, 4)]),
        ] {
            assert!(
                unified_recursion_step(2, &current, &predicted, BlakeMode::Compression).is_err()
            );
        }
    }

    #[test]
    fn removing_a_component_counts_as_compression() {
        let current = shape(&[(128, 3)], &[(7, 1)]);
        let predicted = shape(&[(128, 3)], &[]);
        assert_eq!(
            unified_recursion_step(2, &current, &predicted, BlakeMode::BlakeSpecialOpcodes),
            Ok(false)
        );
    }

    #[test]
    fn zero_entries_are_equivalent_to_missing_components() {
        let current = shape(&[(128, 3), (129, 0)], &[(7, 0)]);
        let predicted = shape(&[(128, 3)], &[(8, 0)]);
        assert!(
            unified_recursion_step(2, &current, &predicted, BlakeMode::BlakeSpecialOpcodes)
                .is_err()
        );
    }
}
