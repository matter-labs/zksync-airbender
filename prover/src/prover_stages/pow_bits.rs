use super::*;

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProofSecurityConfig {
    pub lookup_pow_bits: u32,
    pub quotient_alpha_pow_bits: u32,
    pub quotient_z_pow_bits: u32,
    pub deep_poly_alpha_pow_bits: u32,
    pub foldings_pow_bits: Vec<u32>,
    pub fri_queries_pow_bits: u32,
    pub num_queries: usize,
}

impl ProofSecurityConfig {
    pub fn for_queries_only(
        foldings_number: usize,
        fri_queries_pow_bits: u32,
        num_queries: usize,
    ) -> Self {
        Self {
            lookup_pow_bits: 0,
            quotient_alpha_pow_bits: 0,
            quotient_z_pow_bits: 0,
            deep_poly_alpha_pow_bits: 0,
            foldings_pow_bits: vec![0; foldings_number],
            fri_queries_pow_bits,
            num_queries,
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProofPowChallenges {
    pub lookup_pow_challenge: u64,
    pub quotient_alpha_pow_challenge: u64,
    pub quotient_z_pow_challenge: u64,
    pub deep_poly_alpha_pow_challenge: u64,
    pub foldings_pow_challenges: Vec<u64>,
    pub fri_queries_pow_challenge: u64,
}

#[inline(always)]
pub(crate) fn get_pow_challenge_and_transcript_challenges(
    seed: &mut Seed,
    pow_bits: u32,
    num_elements: usize,
    worker: &Worker,
) -> (u64, Vec<u32>) {
    let pow_challenge;
    if pow_bits > 0 {
        #[cfg(feature = "debug_logs")]
        println!("Searching for PoW for {} bits", pow_bits);
        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        (*seed, pow_challenge) = Transcript::search_pow(seed, pow_bits, worker);
        #[cfg(feature = "timing_logs")]
        println!(
            "PoW for {} took {:?}",
            pow_bits.fri_queries_pow_bits,
            now.elapsed()
        );
    } else {
        #[cfg(feature = "debug_logs")]
        println!("Skip searching for PoW");
        pow_challenge = 0;
    };

    let mut transcript_challenges = if pow_bits > 0 {
        vec![0u32; (num_elements + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)]
    } else {
        vec![0u32; num_elements.next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)]
    };

    Transcript::draw_randomness(seed, &mut transcript_challenges);

    if pow_bits > 0 {
        // Skip first challenge used for pow
        transcript_challenges.remove(0);
    }

    (pow_challenge, transcript_challenges)
}
