// The native input producer and interpreted verifier share this byte format.
#![allow(dead_code)]

#[path = "miri_mock.rs"]
mod miri_mock;

use full_statement_verifier::verifier_common::prover::definitions::SoundnessMode;

#[derive(Clone, Copy)]
pub enum Chain {
    Base,
    Unrolled,
    Unified,
    UnrolledUnified,
    Compression,
}

#[derive(Clone, Copy)]
pub struct Selection {
    pub mode: SoundnessMode,
    pub chain: Chain,
}

impl Selection {
    pub fn verify(self, nds: &mut (impl Iterator<Item = u32> + Send + Sync)) -> [u32; 16] {
        use full_statement_verifier::verifier_common::{
            errors::DebugErrorCreator, USE_REDUCED_BLAKE2_ROUNDS,
        };
        macro_rules! verify {
            ($mode:ident) => {{
                use full_statement_verifier::$mode::*;
                match self.chain {
                    Chain::Base => {
                        verify_unrolled_base_layer::<_, DebugErrorCreator, USE_REDUCED_BLAKE2_ROUNDS>(nds)
                    },
                    Chain::Unrolled => {
                        verify_unrolled_recursion_layer::<_, DebugErrorCreator, USE_REDUCED_BLAKE2_ROUNDS>(nds)
                    },
                    Chain::Unified | Chain::UnrolledUnified => {
                        verify_unified_circuit_recursion_layer::<_, DebugErrorCreator, USE_REDUCED_BLAKE2_ROUNDS>(nds)
                    },
                    Chain::Compression => unreachable!("compression statements use their mode-specific entry"),
                }
            }};
        }
        let output = match (self.mode, self.chain) {
            (SoundnessMode::PessimisticConjecture, Chain::Compression) => {
                full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100_compression_final::<_, DebugErrorCreator, USE_REDUCED_BLAKE2_ROUNDS>(nds)
            }
            (SoundnessMode::EthproofsSoundnessCalc, Chain::Compression) => {
                panic!("Ethproofs compression statement is unavailable")
            }
            (SoundnessMode::PessimisticConjecture, _) => verify!(pessimistic_conjecture),
            (SoundnessMode::EthproofsSoundnessCalc, _) => verify!(ethproofs_soundcalc),
        }
        .expect("full statement verifier rejected input");
        assert!(
            nds.next().is_none(),
            "full statement verifier left NDS words"
        );
        output
    }
}

pub fn encode(expected: &[u32; 16], nds: &[u32]) -> Vec<u8> {
    let mut input = Vec::with_capacity(4 * (expected.len() + nds.len()));
    for word in expected.iter().chain(nds) {
        input.extend_from_slice(&word.to_le_bytes());
    }
    input
}

pub fn decode(input: &[u8]) -> ([u32; 16], impl Iterator<Item = u32> + '_) {
    let (bytes, remainder) = input.as_chunks::<4>();
    assert!(remainder.is_empty(), "partial input word");
    assert!(bytes.len() >= 16, "missing output words");
    let mut words = bytes.iter().map(|b| u32::from_le_bytes(*b));
    let expected = core::array::from_fn(|_| words.next().unwrap());
    (expected, words)
}
