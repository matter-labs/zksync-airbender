use super::*;
use crate::prover_stages::query_producer::BitSource;
use crate::{
    definitions::{Transcript, DIGEST_SIZE_U32_WORDS},
    gkr::whir::WhirCommitment,
};
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
            let array = el.map(|el| F::from_u32_with_reduction(el));
            let coeffs = E::Coeffs::from_array(array);
            E::from_coeffs(coeffs)
        })
        .collect();

    assert!(all_challenges.len() >= num_challenges);
    all_challenges.truncate(num_challenges);

    all_challenges
}

pub fn add_whir_commitment_to_transcript<F: PrimeField, T: ColumnMajorMerkleTreeConstructor<F>>(
    seed: &mut Seed,
    commitment: &WhirCommitment<F, T>,
) {
    let mut transcript_input = Vec::with_capacity(commitment.cap.cap.len() * DIGEST_SIZE_U32_WORDS);
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
