use super::*;
use crate::gkr::whir::WhirCommitment;
use crate::query_utils::BitSource;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use field::FixedArrayConvertible;
use transcript::Transcript;

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

/// Commit a slice of extension-field elements through the generic transcript.
pub fn commit_field_els<F, E, TR>(seed: &mut TR::Seed, els: &[E])
where
    F: PrimeField,
    E: FieldExtension<F>,
    TR: Transcript<F, E>,
{
    TR::commit_extension_field_elements(seed, els);
}

/// Draw `num_challenges` extension-field elements through the generic transcript.
#[track_caller]
pub fn draw_random_field_els<F, E, TR>(seed: &mut TR::Seed, num_challenges: usize) -> Vec<E>
where
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
{
    let mut all_challenges = vec![E::ZERO; num_challenges];
    TR::draw_random_field_elements(seed, &mut all_challenges);

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
pub fn draw_random_field_els_with_pow<F: PrimeField, E: FieldExtension<F>, TR: Transcript<F, E>>(
    seed: &mut TR::Seed,
    num_challenges: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (u64, Vec<E>)
where
    [(); E::DEGREE]: Sized,
{
    let (new_seed, pow_challenge) = TR::search_pow(seed, pow_bits, worker);
    *seed = new_seed;

    // We consumed one top word for the PoW, so draw one extra word and skip it.
    let num_required_words =
        (num_challenges * E::DEGREE + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut transcript_challenges = vec![0u32; num_required_words];
    TR::draw_randomness(seed, &mut transcript_challenges);

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

pub fn add_whir_commitment_to_transcript<F, E, TR, T>(
    seed: &mut TR::Seed,
    commitment: &WhirCommitment<F, T>,
) where
    F: PrimeField,
    E: FieldExtension<F>,
    TR: Transcript<F, E>,
    T: ColumnMajorMerkleTreeConstructor<F>,
{
    let mut transcript_input =
        Vec::with_capacity(commitment.cap.cap.len() * BLAKE2S_DIGEST_SIZE_U32_WORDS);
    commitment.cap.add_into_buffer(&mut transcript_input);

    TR::commit_u32_with_seed(seed, &transcript_input);
}

pub fn draw_query_bits<F, E, TR>(
    seed: &mut TR::Seed,
    num_bits_for_queries: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (u64, BitSource)
where
    F: PrimeField,
    E: FieldExtension<F>,
    TR: Transcript<F, E>,
{
    let (new_seed, pow_challenge) = TR::search_pow(seed, pow_bits, worker);
    *seed = new_seed;
    let num_required_words =
        num_bits_for_queries.next_multiple_of(u32::BITS as usize) / (u32::BITS as usize);
    // we used 1 top word for PoW
    let num_required_words_padded =
        (num_required_words + 1).next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut source = vec![0u32; num_required_words_padded];
    TR::draw_randomness(seed, &mut source);
    // skip first word
    let source = source[1..].to_vec();

    (pow_challenge, BitSource::new(source))
}
