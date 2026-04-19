use core::convert::Infallible;

pub trait ErrorCreator {
    type Error;

    fn gkr_sumcheck_round_failed(layer: usize, round: usize) -> Self::Error;
    fn gkr_final_step_check_failed(layer: usize) -> Self::Error;
    fn gkr_cache_relation_failed(layer: usize) -> Self::Error;
    fn gkr_grand_product_check_failed() -> Self::Error;
    fn gkr_lookup_identity_failed(lookup_type: usize) -> Self::Error;
    fn whir_sumcheck_failed(round: usize) -> Self::Error;
    fn whir_fold_agreement_failed(query: usize) -> Self::Error;
    fn whir_merkle_path_failed(query: usize) -> Self::Error;
    fn whir_final_constraint_failed() -> Self::Error;
}

#[derive(Clone, Debug)]
pub enum VerificationError {
    GkrSumcheckRoundFailed { layer: usize, round: usize },
    GkrFinalStepCheckFailed { layer: usize },
    GkrCacheRelationFailed { layer: usize },
    GkrGrandProductCheckFailed,
    GkrLookupIdentityFailed { lookup_type: usize },
    WhirSumcheckFailed { round: usize },
    WhirFoldAgreementFailed { query: usize },
    WhirMerklePathFailed { query: usize },
    WhirFinalConstraintFailed,
}

pub struct DebugErrorCreator;

impl ErrorCreator for DebugErrorCreator {
    type Error = VerificationError;

    #[inline(always)]
    fn gkr_sumcheck_round_failed(layer: usize, round: usize) -> VerificationError {
        VerificationError::GkrSumcheckRoundFailed { layer, round }
    }
    #[inline(always)]
    fn gkr_final_step_check_failed(layer: usize) -> VerificationError {
        VerificationError::GkrFinalStepCheckFailed { layer }
    }
    #[inline(always)]
    fn gkr_cache_relation_failed(layer: usize) -> VerificationError {
        VerificationError::GkrCacheRelationFailed { layer }
    }
    #[inline(always)]
    fn gkr_grand_product_check_failed() -> VerificationError {
        VerificationError::GkrGrandProductCheckFailed
    }
    #[inline(always)]
    fn gkr_lookup_identity_failed(lookup_type: usize) -> VerificationError {
        VerificationError::GkrLookupIdentityFailed { lookup_type }
    }
    #[inline(always)]
    fn whir_sumcheck_failed(round: usize) -> VerificationError {
        VerificationError::WhirSumcheckFailed { round }
    }
    #[inline(always)]
    fn whir_fold_agreement_failed(query: usize) -> VerificationError {
        VerificationError::WhirFoldAgreementFailed { query }
    }
    #[inline(always)]
    fn whir_merkle_path_failed(query: usize) -> VerificationError {
        VerificationError::WhirMerklePathFailed { query }
    }
    #[inline(always)]
    fn whir_final_constraint_failed() -> VerificationError {
        VerificationError::WhirFinalConstraintFailed
    }
}

pub struct PanicErrorCreator;

impl ErrorCreator for PanicErrorCreator {
    type Error = Infallible;

    #[inline(always)]
    fn gkr_sumcheck_round_failed(layer: usize, round: usize) -> Infallible {
        panic!("GKR sumcheck failed: layer {layer} round {round}")
    }
    #[inline(always)]
    fn gkr_final_step_check_failed(layer: usize) -> Infallible {
        panic!("GKR final step check failed: layer {layer}")
    }
    #[inline(always)]
    fn gkr_cache_relation_failed(layer: usize) -> Infallible {
        panic!("GKR cache relation failed: layer {layer}")
    }
    #[inline(always)]
    fn gkr_grand_product_check_failed() -> Infallible {
        panic!("GKR grand product check failed")
    }
    #[inline(always)]
    fn gkr_lookup_identity_failed(lookup_type: usize) -> Infallible {
        panic!("GKR lookup identity failed: type {lookup_type}")
    }
    #[inline(always)]
    fn whir_sumcheck_failed(round: usize) -> Infallible {
        panic!("WHIR sumcheck failed: round {round}")
    }
    #[inline(always)]
    fn whir_fold_agreement_failed(query: usize) -> Infallible {
        panic!("WHIR fold agreement failed: query {query}")
    }
    #[inline(always)]
    fn whir_merkle_path_failed(query: usize) -> Infallible {
        panic!("WHIR merkle path failed: query {query}")
    }
    #[inline(always)]
    fn whir_final_constraint_failed() -> Infallible {
        panic!("WHIR final constraint failed")
    }
}
