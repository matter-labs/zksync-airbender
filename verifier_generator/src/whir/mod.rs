use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub mod common;
pub mod final_round;
pub mod initial_round;
pub mod internal_rounds;

pub use common::generate_whir_common;
pub use final_round::generate_whir_final_round;
pub use initial_round::generate_whir_inlined;
pub use internal_rounds::generate_whir_internal_rounds;

/// Generate a unified `verify_whir` function that chains initial -> internal -> final rounds.
/// Creates the hash buffer and passes it + hasher to each round.
pub fn generate_whir_verify<MW: MersenneWrapper>(whir_hash_buf_size: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();

    quote! {
        pub const WHIR_HASH_BUF_SIZE: usize = #whir_hash_buf_size;

        /// Run the full WHIR verification: initial round, all internal rounds, final round.
        #[allow(unused_braces, unused_mut, unused_variables, unused_unsafe, clippy::needless_borrow)]
        pub fn verify_whir<I: NonDeterminismSource>(
            ts: &mut TranscriptState,
            batching_challenge: #quartic_struct,
            setup_cap: &[u32; SETUP_CAP_WORDS],
            memory_cap: &[u32; MEM_CAP_WORDS],
            witness_cap: &[u32; WIT_CAP_WORDS],
        ) -> Result<(), WhirVerificationError> {
            let mut hash_buf = AlignedArray64::<u32, WHIR_HASH_BUF_SIZE>::new_uninit();
            let (mut claim, mut cap) = verify_initial_whir_round::<I>(
                ts, &mut hash_buf, batching_challenge, setup_cap, memory_cap, witness_cap,
            )?;
            let mut round_idx = 1;
            while round_idx <= NUM_INTERNAL_ROUNDS {
                let (new_claim, new_cap) = verify_internal_whir_round::<I>(
                    ts, &mut hash_buf, claim, &cap, round_idx,
                )?;
                claim = new_claim;
                cap = new_cap;
                round_idx += 1;
            }
            verify_final_whir_round::<I>(ts, &mut hash_buf, claim, &cap)?;
            Ok(())
        }
    }
}
