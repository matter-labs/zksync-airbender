use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub mod common;
pub mod rounds;

pub use common::generate_whir_common;
pub use rounds::{
    generate_whir_final_round, generate_whir_initial_round, generate_whir_internal_rounds,
};

pub fn generate_whir_verify<MW: MersenneWrapper>(whir_hash_buf_size: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();

    quote! {
        pub const WHIR_HASH_BUF_SIZE: usize = #whir_hash_buf_size;

        pub fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
            initial_transcript: &ConcreteInitialTranscript,
            ts: &mut TranscriptState,
            batching_challenge: #quartic_struct,
            base_layer_claims: &[#quartic_struct],
            z_initial: &[#quartic_struct],
        ) -> Result<(), E::Error> {
            let mut hash_buf = AlignedArray64::<u32, WHIR_HASH_BUF_SIZE>::new_uninit();
            let mut accumulator = ::verifier_common::whir::WhirAccumulator::<
                #quartic_struct, MAX_POW_ENTRIES,
            >::new(#quartic_one);
            let (mut claim, mut cap) = verify_initial_whir_round::<I, E>(
                initial_transcript,
                ts, &mut hash_buf, batching_challenge, base_layer_claims,
                z_initial, &mut accumulator,
            )?;
            let mut round_idx = 1;
            while round_idx <= NUM_INTERNAL_ROUNDS {
                let (new_claim, new_cap) = verify_internal_whir_round::<I, E>(
                    ts, &mut hash_buf, claim, &cap, round_idx,
                    z_initial, &mut accumulator,
                )?;
                claim = new_claim;
                cap = new_cap;
                round_idx += 1;
            }
            verify_final_whir_round::<I, E>(
                ts, &mut hash_buf, claim, &cap, z_initial, &mut accumulator,
            )?;
            Ok(())
        }
    }
}
