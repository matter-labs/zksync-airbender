use verifier_common::transcript::Blake2sBufferingTranscript;

pub fn compute_end_params<'a, const REDUCED_ROUNDS: bool>(
    final_pc: u32,
    flattened_setup_caps: impl Iterator<Item = &'a [u32]>,
) -> [u32; 8] {
    let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
    let mut buffer = [0u32; 16];
    buffer[0] = final_pc;
    hasher.absorb(&buffer);
    for cap in flattened_setup_caps {
        hasher.absorb(cap);
    }
    hasher.finalize_reset().0
}

/// A recursion hash chain: `hash` is always blake(`preimage`), and `preimage`
/// is `[previous hash (or zeroes at the base) || latest end_params]`.
///
/// The pairing is an invariant the verifier checks, so the fields are private —
/// a chain can only be constructed at the base ([`RecursionChain::begin`]) and
/// advanced one verified program at a time ([`RecursionChain::extend`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecursionChain<const REDUCED_ROUNDS: bool> {
    hash: [u32; 8],
    preimage: [u32; 16],
}

impl<const REDUCED_ROUNDS: bool> RecursionChain<REDUCED_ROUNDS> {
    #[must_use]
    pub fn begin(base_end_params: &[u32; 8]) -> Self {
        let mut preimage = [0u32; 16];
        preimage[8..].copy_from_slice(base_end_params);
        Self {
            hash: Self::hash_preimage(&preimage),
            preimage,
        }
    }

    pub fn extend(&mut self, end_params: &[u32; 8]) {
        if self.preimage[8..] == end_params[..] {
            return;
        }
        let mut preimage = [0u32; 16];
        preimage[..8].copy_from_slice(&self.hash);
        preimage[8..].copy_from_slice(end_params);
        self.hash = Self::hash_preimage(&preimage);
        self.preimage = preimage;
    }

    #[must_use]
    pub const fn hash(&self) -> [u32; 8] {
        self.hash
    }

    #[must_use]
    pub const fn preimage(&self) -> [u32; 16] {
        self.preimage
    }

    fn hash_preimage(preimage: &[u32; 16]) -> [u32; 8] {
        let mut hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
        hasher.absorb(preimage);
        hasher.finalize_reset().0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursion_chain_is_consistent() {
        let ep_base = [1u32, 2, 3, 4, 5, 6, 7, 8];
        let mut chain = RecursionChain::<true>::begin(&ep_base);
        assert_eq!(&chain.preimage()[8..], &ep_base);

        let hash_base = chain.hash();
        let ep_step = [9u32, 10, 11, 12, 13, 14, 15, 16];
        chain.extend(&ep_step);
        assert_ne!(
            chain.hash(),
            hash_base,
            "a new program must advance the chain"
        );
        assert_eq!(&chain.preimage()[..8], &hash_base);
        assert_eq!(&chain.preimage()[8..], &ep_step);

        // re-chaining the same program is a no-op.
        let snapshot = chain;
        chain.extend(&ep_step);
        assert_eq!(chain, snapshot);
    }
}
