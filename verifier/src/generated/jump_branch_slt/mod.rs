#[path = "../common/mod.rs"]
pub mod common;
pub mod constants;
pub mod gkr;
pub mod whir;
pub use gkr::verify_gkr_sumcheck;
use verifier_common::gkr::GKRVerificationError;
use verifier_common::non_determinism_source::NonDeterminismSource;
#[derive(Clone, Debug)]
pub enum VerificationError {
    Gkr(GKRVerificationError),
    Whir(common::WhirVerificationError),
}
#[doc = r" Run the full GKR + WHIR verification pipeline."]
#[allow(unused_braces, unused_mut, unused_variables)]
pub fn verify_all<I: NonDeterminismSource>() -> Result<(), VerificationError> {
    let gkr_output = verify_gkr_sumcheck::<I>().map_err(VerificationError::Gkr)?;
    let mut seed = gkr_output.whir_transcript_seed;
    whir::verify_whir::<I>(
        &mut seed,
        gkr_output.whir_batching_challenge,
        &gkr_output.setup_cap,
        &gkr_output.memory_cap,
        &gkr_output.witness_cap,
    )
    .map_err(VerificationError::Whir)
}
