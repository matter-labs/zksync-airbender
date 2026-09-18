pub use gpu_gkr::forward::GkrMemoryPolicy;
pub use gpu_trace::trace::holder::{
    OpeningStrategy, WitnessCommitmentStrategy, WitnessPostCommitStorage,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WitnessOpeningStrategy {
    #[default]
    ReuseCosets,
    Recompute(OpeningStrategy),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WitnessMemoryPolicy {
    pub commitment: WitnessCommitmentStrategy,
    pub post_commitment: WitnessPostCommitStorage,
    pub opening: WitnessOpeningStrategy,
}

impl WitnessMemoryPolicy {
    pub const fn is_valid(self) -> bool {
        use WitnessCommitmentStrategy as Commit;
        use WitnessPostCommitStorage as Store;
        let storage_available = matches!(
            (self.commitment, self.post_commitment),
            (Commit::AllCosets, _)
                | (
                    Commit::PerCoset,
                    Store::RawEvaluations | Store::RawAndMonomials
                )
                | (Commit::InPlace, Store::RawEvaluations)
        );
        storage_available
            && matches!(
                (self.post_commitment, self.opening),
                (Store::RawAndCosets, WitnessOpeningStrategy::ReuseCosets)
                    | (
                        Store::RawEvaluations | Store::RawAndMonomials,
                        WitnessOpeningStrategy::Recompute(_)
                    )
            )
    }

    pub fn candidates() -> impl Iterator<Item = Self> {
        [
            WitnessCommitmentStrategy::AllCosets,
            WitnessCommitmentStrategy::PerCoset,
            WitnessCommitmentStrategy::InPlace,
        ]
        .into_iter()
        .flat_map(|commitment| {
            [
                WitnessPostCommitStorage::RawEvaluations,
                WitnessPostCommitStorage::RawAndMonomials,
                WitnessPostCommitStorage::RawAndCosets,
            ]
            .into_iter()
            .flat_map(move |post_commitment| {
                std::iter::once(WitnessOpeningStrategy::ReuseCosets)
                    .chain(OPENINGS.map(WitnessOpeningStrategy::Recompute))
                    .map(move |opening| Self {
                        commitment,
                        post_commitment,
                        opening,
                    })
                    .filter(|policy| policy.is_valid())
            })
        })
    }
}

const OPENINGS: [OpeningStrategy; 3] = [
    OpeningStrategy::AllCosets,
    OpeningStrategy::PerCoset,
    OpeningStrategy::InPlace,
];

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProofMemoryPolicy {
    pub gkr: GkrMemoryPolicy,
    pub setup: OpeningStrategy,
    pub memory: OpeningStrategy,
    pub witness: WitnessMemoryPolicy,
}

impl ProofMemoryPolicy {
    pub fn candidates() -> impl Iterator<Item = Self> {
        OPENINGS.into_iter().flat_map(|setup| {
            OPENINGS.into_iter().flat_map(move |memory| {
                WitnessMemoryPolicy::candidates().map(move |witness| Self {
                    gkr: GkrMemoryPolicy::Materialize,
                    setup,
                    memory,
                    witness,
                })
            })
        })
    }
}
