use crate::upstream::{GKRCircuitArtifact, PrimeField};
use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use serde::Serialize;

pub type WitnessArtifactFingerprint = [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];

const FINGERPRINT_DOMAIN: &[u8] = b"airbender.gpu.witness-artifact.v1\0";

/// Hash the complete serialized GKR artifact used by committed GPU witness code.
///
/// The byte length frames the canonical JSON before zero-padding it to the
/// word-oriented Blake2s API, so distinct trailing-zero inputs remain distinct.
pub fn witness_artifact_fingerprint<F>(
    artifact: &GKRCircuitArtifact<F>,
) -> Result<WitnessArtifactFingerprint, serde_json::Error>
where
    F: PrimeField,
    GKRCircuitArtifact<F>: Serialize,
{
    let serialized = serde_json::to_vec(artifact)?;
    let serialized_len = u64::try_from(serialized.len()).expect("artifact length fits u64");
    let mut framed = Vec::with_capacity(FINGERPRINT_DOMAIN.len() + 8 + serialized.len() + 3);
    framed.extend_from_slice(FINGERPRINT_DOMAIN);
    framed.extend_from_slice(&serialized_len.to_le_bytes());
    framed.extend_from_slice(&serialized);
    framed.resize(framed.len().next_multiple_of(size_of::<u32>()), 0);

    let words: Vec<u32> = framed
        .chunks_exact(size_of::<u32>())
        .map(|bytes| u32::from_le_bytes(bytes.try_into().expect("four-byte chunk")))
        .collect();
    debug_assert!(!words.is_empty());

    let final_words = match words.len() % BLAKE2S_BLOCK_SIZE_U32_WORDS {
        0 => BLAKE2S_BLOCK_SIZE_U32_WORDS,
        remainder => remainder,
    };
    let final_start = words.len() - final_words;
    let mut state = Blake2sState::new();
    for block in words[..final_start].chunks_exact(BLAKE2S_BLOCK_SIZE_U32_WORDS) {
        state.absorb::<false>(block.try_into().expect("complete Blake2s block"));
    }
    let mut final_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    final_block[..final_words].copy_from_slice(&words[final_start..]);
    let mut digest = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    state.absorb_final_block::<false>(&final_block, final_words, &mut digest);
    Ok(digest)
}
