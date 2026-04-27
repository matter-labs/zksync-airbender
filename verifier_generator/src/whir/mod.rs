use proc_macro2::TokenStream;
use quote::quote;

use crate::field_wrapper::FieldWrapper;

pub mod common;
pub mod rounds;

pub use common::generate_whir_common;
pub use rounds::{
    generate_whir_final_round, generate_whir_initial_round, generate_whir_internal_rounds,
};

pub fn generate_whir_verify<MW: FieldWrapper>(whir_hash_buf_size: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();

    let labels = quote! {[
        "WHIR SINGLE ROUND 0",  "WHIR SINGLE ROUND 1",  "WHIR SINGLE ROUND 2",  "WHIR SINGLE ROUND 3",
        "WHIR SINGLE ROUND 4",  "WHIR SINGLE ROUND 5",  "WHIR SINGLE ROUND 6",  "WHIR SINGLE ROUND 7",
        "WHIR SINGLE ROUND 8",  "WHIR SINGLE ROUND 9",  "WHIR SINGLE ROUND 10", "WHIR SINGLE ROUND 11",
        "WHIR SINGLE ROUND 12", "WHIR SINGLE ROUND 13", "WHIR SINGLE ROUND 14", "WHIR SINGLE ROUND 15",
        "WHIR SINGLE ROUND 16", "WHIR SINGLE ROUND 17", "WHIR SINGLE ROUND 18", "WHIR SINGLE ROUND 19",
        "WHIR SINGLE ROUND 20", "WHIR SINGLE ROUND 21", "WHIR SINGLE ROUND 22", "WHIR SINGLE ROUND 23",
        "WHIR SINGLE ROUND 24", "WHIR SINGLE ROUND 25", "WHIR SINGLE ROUND 26", "WHIR SINGLE ROUND 27",
    ]};
    quote! {
        #[cfg(feature = "verifier_stats")]
        const _: () = assert!(
            NUM_INTERNAL_ROUNDS + 1 < #labels.len(),
            "WHIR stats labels array is too small for NUM_INTERNAL_ROUNDS"
        );

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
            #[cfg(feature = "verifier_stats")]
                verifier_common::stats::log("WHIR BATCHED ROUND 0");

            let mut round_idx = 1;
            while round_idx <= NUM_INTERNAL_ROUNDS {
                let (new_claim, new_cap) = verify_internal_whir_round::<I, E>(
                    ts, &mut hash_buf, claim, &cap, round_idx,
                    z_initial, &mut accumulator,
                )?;
                #[cfg(feature = "verifier_stats")]
                    verifier_common::stats::log(#labels[round_idx]);
                claim = new_claim;
                cap = new_cap;
                round_idx += 1;
            }
            verify_final_whir_round::<I, E>(
                ts, &mut hash_buf, claim, &cap, z_initial, &mut accumulator,
            )?;
            #[cfg(feature = "verifier_stats")]
                    verifier_common::stats::log(#labels[NUM_INTERNAL_ROUNDS+1]);

            Ok(())
        }
    }
}
