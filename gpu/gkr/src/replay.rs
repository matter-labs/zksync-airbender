//! Per-request values that replayed GKR graphs patch into kernel arguments.

use gpu_core::primitives::field::{BF, E4};

use crate::upstream::GKRExternalChallenges;

pub struct GkrReplayValues {
    pub external_challenges: GKRExternalChallenges<BF, E4>,
    pub inits_and_teardowns_top_bits: Vec<u32>,
}
