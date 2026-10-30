//! A resource-bounded final-recursion policy; it does not prove a terminal profile impossible.

use verifier_common::fsv_binaries::BlakeMode;

/// Proof counts in the well-founded order used after the first final-program transition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FinalProofShape {
    pub unified_chunks: usize,
    pub delegation_proofs: usize,
}

/// Typed proving/continuation failure. Compatibility entry points return its Display text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineError {
    Operation(String),
    NoProgress {
        final_blake: BlakeMode,
        round: usize,
        before: FinalProofShape,
        after: FinalProofShape,
        executed_cycles: u64,
        unified_chunk_capacity: u64,
    },
}

impl std::fmt::Display for PipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Operation(message) => f.write_str(message),
            Self::NoProgress { final_blake, round, before, after, executed_cycles, unified_chunk_capacity } => write!(f,
                "NoProgress: final Blake {} round {round} did not reduce (unified chunks, delegation proofs): ({}, {}) -> ({}, {}); terminal target is (1, {}); produced proof executed {executed_cycles} cycles with unified chunk capacity {unified_chunk_capacity}. One bridge-to-final transition is allowed; subsequent rounds require strict lexicographic progress. No verifier fallback was attempted",
                final_blake.tag(), before.unified_chunks, before.delegation_proofs,
                after.unified_chunks, after.delegation_proofs,
                usize::from(*final_blake != BlakeMode::BlakeSpecialOpcodes)),
        }
    }
}
impl std::error::Error for PipelineError {}
impl From<String> for PipelineError {
    fn from(message: String) -> Self {
        Self::Operation(message)
    }
}

pub(super) struct FinalRoundSummary {
    pub shape: FinalProofShape,
    pub converged: bool,
    pub executed_cycles: u64,
    pub unified_chunk_capacity: u64,
}

pub(super) fn drive_final_rounds<S>(
    mut state: S,
    final_blake: BlakeMode,
    mut prove: impl FnMut(S, usize) -> Result<S, PipelineError>,
    summarize: impl Fn(&S) -> FinalRoundSummary,
) -> Result<S, PipelineError> {
    let mut round = 0;
    let mut previous = None;
    loop {
        state = prove(state, round)?;
        round += 1;
        let summary = summarize(&state);
        log::debug!(
            "final recursion shape {:?}, {} cycles, {} rows per unified chunk",
            summary.shape,
            summary.executed_cycles,
            summary.unified_chunk_capacity
        );
        if summary.converged {
            return Ok(state);
        }
        // The bridge proves a different program. Its first final-program transition
        // may increase either count; only repeated final-program rounds must decrease.
        if let Some(before) = previous {
            if summary.shape >= before {
                return Err(PipelineError::NoProgress {
                    final_blake,
                    round,
                    before,
                    after: summary.shape,
                    executed_cycles: summary.executed_cycles,
                    unified_chunk_capacity: summary.unified_chunk_capacity,
                });
            }
        }
        previous = Some(summary.shape);
    }
}

pub(super) fn finish_operation<B, T>(
    backend: &mut Option<B>,
    result: Result<T, PipelineError>,
) -> Result<T, PipelineError> {
    if result.is_err() {
        // ExecutionBackend's Drop contract drains accepted work and joins workers
        // before setup/allocation owners are destroyed. Do this before returning.
        drop(backend.take());
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{mpsc, Arc, Weak};
    use std::thread::JoinHandle;

    struct Producer {
        commands: Option<mpsc::Sender<mpsc::Sender<()>>>,
        worker: Option<JoinHandle<()>>,
    }
    impl Producer {
        fn new() -> (Self, Arc<AtomicBool>, Weak<Vec<u8>>) {
            let allocation = Arc::new(vec![0u8; 8192]);
            let weak = Arc::downgrade(&allocation);
            let joined = Arc::new(AtomicBool::new(false));
            let complete = Arc::clone(&joined);
            let (commands, receiver) = mpsc::channel::<mpsc::Sender<()>>();
            let worker = std::thread::spawn(move || {
                for ack in receiver {
                    std::hint::black_box(&allocation);
                    ack.send(()).unwrap();
                }
                drop(allocation);
                complete.store(true, Ordering::SeqCst);
            });
            (
                Self {
                    commands: Some(commands),
                    worker: Some(worker),
                },
                joined,
                weak,
            )
        }
        fn prove(&mut self) {
            let (ack, done) = mpsc::channel();
            self.commands.as_ref().unwrap().send(ack).unwrap();
            done.recv().unwrap();
        }
    }
    impl Drop for Producer {
        fn drop(&mut self) {
            drop(self.commands.take());
            self.worker.take().unwrap().join().unwrap();
        }
    }

    fn summary(shape: &(usize, usize)) -> FinalRoundSummary {
        FinalRoundSummary {
            shape: FinalProofShape {
                unified_chunks: shape.0,
                delegation_proofs: shape.1,
            },
            converged: shape == &(1, 0),
            executed_cycles: 10_696_157,
            unified_chunk_capacity: 1 << 23,
        }
    }

    #[test]
    fn special_opcodes_final_stall_stops_after_the_transition() {
        let mut calls = 0;
        let error = drive_final_rounds(
            (1, 1),
            BlakeMode::BlakeSpecialOpcodes,
            |_, _| {
                calls += 1;
                // Bound the pre-fix reproduction so the regression itself cannot loop forever.
                if calls > 2 {
                    return Err(PipelineError::Operation(
                        "unexpected third final round".into(),
                    ));
                }
                Ok((2, 0))
            },
            summary,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            PipelineError::NoProgress {
                round: 2,
                final_blake: BlakeMode::BlakeSpecialOpcodes,
                before: FinalProofShape {
                    unified_chunks: 2,
                    delegation_proofs: 0
                },
                after: FinalProofShape {
                    unified_chunks: 2,
                    delegation_proofs: 0
                },
                executed_cycles: 10_696_157,
                unified_chunk_capacity: 8_388_608
            }
        ));
        assert_eq!(calls, 2);
        let text = error.to_string();
        assert!(text.contains("special_opcodes_extension"));
        assert!(text.contains("terminal target is (1, 0)"));
        assert!(text.contains("10696157"));
    }

    #[test]
    fn a_failed_operation_joins_its_producer_and_releases_allocation() {
        let (producer, joined, allocation) = Producer::new();
        let mut backend = Some(producer);
        let mut calls = 0;
        let result = drive_final_rounds(
            (1, 1),
            BlakeMode::BlakeSpecialOpcodes,
            |_, _| {
                backend.as_mut().unwrap().prove();
                calls += 1;
                if calls > 2 {
                    return Err(PipelineError::Operation(
                        "unexpected third final round".into(),
                    ));
                }
                Ok((2, 0))
            },
            summary,
        );
        let result = finish_operation(&mut backend, result);
        assert!(matches!(result, Err(PipelineError::NoProgress { .. })));
        assert!(
            backend.is_none(),
            "failed operation must release the owned backend before returning"
        );
        assert!(
            joined.load(Ordering::SeqCst),
            "producer worker must be joined"
        );
        assert!(
            allocation.upgrade().is_none(),
            "producer allocation must be released"
        );
    }

    #[test]
    fn a_successful_operation_keeps_the_session_available() {
        let (producer, joined, allocation) = Producer::new();
        let mut backend = Some(producer);
        finish_operation(&mut backend, Ok(())).unwrap();
        assert!(backend.is_some());
        assert!(!joined.load(Ordering::SeqCst));
        assert!(allocation.upgrade().is_some());
        drop(backend);
        assert!(joined.load(Ordering::SeqCst));
        assert!(allocation.upgrade().is_none());
    }
    #[test]
    fn every_strict_reduction_is_accepted_after_the_transition() {
        let mut sequence = [(3, 0), (2, 5), (2, 4), (1, 0)].into_iter();
        let result = drive_final_rounds(
            (1, 1),
            BlakeMode::BlakeSpecialOpcodes,
            |_, _| Ok(sequence.next().expect("a reducing path must finish")),
            summary,
        )
        .unwrap();
        assert_eq!(result, (1, 0));
        assert!(sequence.next().is_none());
    }

    #[test]
    fn equal_unified_count_with_more_delegations_is_refused() {
        let mut sequence = [(2, 0), (2, 1)].into_iter();
        let error = drive_final_rounds(
            (1, 1),
            BlakeMode::BlakeSpecialOpcodes,
            |_, _| {
                Ok(sequence
                    .next()
                    .expect("must stop at the first non-reduction"))
            },
            summary,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            PipelineError::NoProgress {
                before: FinalProofShape {
                    unified_chunks: 2,
                    delegation_proofs: 0
                },
                after: FinalProofShape {
                    unified_chunks: 2,
                    delegation_proofs: 1
                },
                ..
            }
        ));
    }

    #[test]
    fn terminal_success_uses_the_existing_per_blake_predicate() {
        fn proof(unified: usize, delegations: usize) -> crate::ProgramProof {
            use prover::gkr::prover::GKRProof;
            use prover::gkr::whir::whir_proof::{
                WhirBaseLayerCommitmentAndQueries, WhirCommitment, WhirPolyCommitProof,
            };
            let commitment = || WhirBaseLayerCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: Default::default(),
                    _marker: Default::default(),
                },
                num_columns: 0,
                evals: Vec::new(),
                queries: Vec::new(),
            };
            let gkr = GKRProof {
                external_challenges: Default::default(),
                final_explicit_evaluations: Default::default(),
                sumcheck_intermediate_values: Default::default(),
                whir_proof: WhirPolyCommitProof {
                    setup_commitment: commitment(),
                    memory_commitment: commitment(),
                    witness_commitment: commitment(),
                    batching_challenge_pow_nonce: 0,
                    base_sumcheck_polys: Vec::new(),
                    base_folding_pow_nonces: Vec::new(),
                    base_queries_pow_nonce: 0,
                    intermediate_whir_oracles: Vec::new(),
                    final_monomials: Vec::new(),
                    whir_schedule: Default::default(),
                },
                grand_product_accumulator_computed: Default::default(),
                inits_and_teardowns_top_bits: Vec::new(),
                lookup_challenges_pow_nonce: 0,
            };
            crate::ProgramProof {
                riscv_proofs: [(0, vec![gkr.clone(); unified])].into_iter().collect(),
                compiled_riscv_circuits: Default::default(),
                inits_and_teardown_proofs: Vec::new(),
                inits_and_teardowns_circuit: None,
                delegation_proofs: [(1, vec![gkr; delegations])].into_iter().collect(),
                compiled_delegation_circuits: Default::default(),
                register_final_values: Vec::new(),
                final_pc: 0,
                final_timestamp: 4,
                end_params: [0; 8],
                recursion_chain_preimage: None,
                recursion_chain_hash: None,
                pow_challenge: 0,
                num_it_circuits: None,
            }
        }
        for mode in [BlakeMode::Compression, BlakeMode::BlakeSpecialOpcodes] {
            let target = (1, usize::from(mode != BlakeMode::BlakeSpecialOpcodes));
            for shape in [(1, 0), (1, 1), (2, 0), (2, 1)] {
                assert_eq!(
                    crate::unified_recursion_has_converged(&proof(shape.0, shape.1), mode),
                    shape == target
                );
            }
            let error = PipelineError::NoProgress {
                final_blake: mode,
                round: 2,
                before: FinalProofShape {
                    unified_chunks: 2,
                    delegation_proofs: 2,
                },
                after: FinalProofShape {
                    unified_chunks: 2,
                    delegation_proofs: 2,
                },
                executed_cycles: 12_345_678,
                unified_chunk_capacity: 1 << 23,
            };
            assert!(
                error
                    .to_string()
                    .contains(&format!("terminal target is ({}, {})", target.0, target.1)),
                "the diagnostic target must agree with the existing predicate"
            );
            let mut calls = 0;
            let result = drive_final_rounds(
                target,
                mode,
                |_, _| {
                    calls += 1;
                    Ok(target)
                },
                |shape| FinalRoundSummary {
                    converged: crate::unified_recursion_has_converged(
                        &proof(shape.0, shape.1),
                        mode,
                    ),
                    ..summary(shape)
                },
            )
            .unwrap();
            assert_eq!(result, target);
            assert_eq!(
                calls, 1,
                "the final program must still run once after the bridge"
            );
        }
    }
}
