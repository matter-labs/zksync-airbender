#[path = "../common/mod.rs"]
pub mod common;
pub mod constants;
pub mod gkr;
pub mod whir;
pub use gkr::verify_gkr;
use verifier_common::errors::ErrorCreator;
use verifier_common::non_determinism_source::NonDeterminismSource;
#[allow(unused_braces, unused_mut, unused_variables)]
pub fn verify<I: NonDeterminismSource, E: ErrorCreator>() -> Result<(), E::Error> {
    let gkr_output = verify_gkr::<I, E>()?;
    let mut ts = ::verifier_common::structs::TranscriptState::new(gkr_output.whir_transcript_seed);
    whir::verify_whir::<I, E>(
        &mut ts,
        gkr_output.whir_batching_challenge,
        &gkr_output.oracle_caps,
    )
}
