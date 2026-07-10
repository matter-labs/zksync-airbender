use super::*;
use crate::query_utils::BitSource;
use crate::{definitions::Transcript, gkr::whir::WhirCommitment};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use field::FixedArrayConvertible;
use transcript::Seed;

pub fn flatten_field_els_into<F: PrimeField, E: FieldExtension<F>>(src: &[E], dst: &mut Vec<u32>)
where
    [(); E::DEGREE]: Sized,
{
    for el in src.iter() {
        let coeffs = E::into_coeffs(*el)
            .into_array::<{ E::DEGREE }>()
            .map(|el: F| el.as_u32_raw_repr_reduced());
        dst.extend(coeffs);
    }
}

pub fn commit_field_els<F: PrimeField, E: FieldExtension<F>>(seed: &mut Seed, els: &[E])
where
    [(); E::DEGREE]: Sized,
{
    let mut transcript_input = Vec::with_capacity(els.len() * E::DEGREE);
    flatten_field_els_into(els, &mut transcript_input);

    Transcript::commit_with_seed(seed, &transcript_input);
}

#[track_caller]
pub fn draw_random_field_els<F: PrimeField, E: FieldExtension<F>>(
    seed: &mut Seed,
    num_challenges: usize,
) -> Vec<E>
where
    [(); E::DEGREE]: Sized,
{
    let mut transcript_challenges =
        vec![0u32; (num_challenges * E::DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    let mut all_challenges: Vec<E> = transcript_challenges
        .as_chunks::<{ E::DEGREE }>()
        .0
        .into_iter()
        .map(|el| {
            let array = el.map(|el| F::from_raw_repr_with_reduction(el));
            let coeffs = E::Coeffs::from_array(array);
            E::from_coeffs(coeffs)
        })
        .collect();

    assert!(all_challenges.len() >= num_challenges);
    all_challenges.truncate(num_challenges);

    all_challenges
}

/// Same as [`draw_random_field_els`], but the challenges are gated behind a
/// proof-of-work. The prover grinds `pow_bits` of PoW into the seed (exactly the
/// work the verifier replays via `read_and_verify_pow`) and returns the winning
/// nonce so it can be written into the proof.
///
/// Mirrors the unconditional grind + skip-first-word convention of
/// [`draw_query_bits`]: a PoW round is always performed (trivially so for
/// `pow_bits == 0`, where `search_pow` returns nonce `0`), and the first drawn
/// word — consumed by the PoW — is always skipped. The drawn word count must
/// match the verifier's PoW-aware draw exactly, or the transcripts diverge.
#[track_caller]
pub fn draw_random_field_els_with_pow<F: PrimeField, E: FieldExtension<F>>(
    seed: &mut Seed,
    num_challenges: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (u64, Vec<E>)
where
    [(); E::DEGREE]: Sized,
{
    let (new_seed, pow_challenge) = Transcript::search_pow(seed, pow_bits, worker);
    *seed = new_seed;

    // We consumed one top word for the PoW, so draw one extra word and skip it.
    let num_required_words =
        (num_challenges * E::DEGREE + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut transcript_challenges = vec![0u32; num_required_words];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    // skip first word used for PoW
    let mut all_challenges: Vec<E> = transcript_challenges[1..]
        .as_chunks::<{ E::DEGREE }>()
        .0
        .into_iter()
        .map(|el| {
            let array = el.map(|el| F::from_raw_repr_with_reduction(el));
            let coeffs = E::Coeffs::from_array(array);
            E::from_coeffs(coeffs)
        })
        .collect();

    assert!(all_challenges.len() >= num_challenges);
    all_challenges.truncate(num_challenges);

    (pow_challenge, all_challenges)
}

pub fn add_whir_commitment_to_transcript<F: PrimeField, T: ColumnMajorMerkleTreeConstructor<F>>(
    seed: &mut Seed,
    commitment: &WhirCommitment<F, T>,
) {
    let mut transcript_input =
        Vec::with_capacity(commitment.cap.cap.len() * BLAKE2S_DIGEST_SIZE_U32_WORDS);
    commitment.cap.add_into_buffer(&mut transcript_input);

    Transcript::commit_with_seed(seed, &transcript_input);
}

pub fn draw_query_bits(
    seed: &mut Seed,
    num_bits_for_queries: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (u64, BitSource) {
    let (new_seed, pow_challenge) = Transcript::search_pow(&seed, pow_bits, worker);
    *seed = new_seed;
    let num_required_words =
        num_bits_for_queries.next_multiple_of(u32::BITS as usize) / (u32::BITS as usize);
    // we used 1 top word for PoW
    let num_required_words_padded =
        (num_required_words + 1).next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut source = vec![0u32; num_required_words_padded];
    Transcript::draw_randomness(seed, &mut source);
    // skip first word
    let source = source[1..].to_vec();

    (pow_challenge, BitSource::new(source))
}
