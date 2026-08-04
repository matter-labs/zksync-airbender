#[path = "../../common/mod.rs"]
pub mod common;
pub mod constants;
pub mod gkr;
pub mod whir;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::GKRExternalChallenges;
pub fn verify<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    nd_source: &mut I,
) -> Result<constants::ConcreteVerifierOutput, E::Error> {
    ::verifier_common::verify_impl::<
        I,
        E,
        BabyBearField,
        BabyBearExt4,
        { constants::INIT_AND_TEARDOWN_SETS },
        { constants::EXTERNAL_CHALLENGES_FLATTENED_SIZE },
        { constants::CAP_SIZE },
        { constants::NUM_MEMORY_COMMITS },
        { constants::NUM_WITNESS_COMMITS },
        { constants::NUM_SETUP_COMMITS },
        { constants::PADDING_WORDS },
        { constants::GKR_ROUNDS },
        { constants::GKR_ADDRS },
        gkr::VerifierImplementation,
    >(external_challenges, nd_source)
}
