pub use gpu_trace::trace::holder::OpeningPolicy;

/// WHIR choices available after a full witness commitment. Recompute releases
/// the committed cosets immediately and retains only raw evaluations through
/// GKR and initial WHIR batching.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FullWitnessWhirPolicy {
    #[default]
    RetainCosets,
    Recompute(OpeningPolicy),
}

/// Opening choices must use only representations preserved by commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitnessMemoryPolicy {
    FullMaterialization {
        whir: FullWitnessWhirPolicy,
    },
    /// Commit through one coset workspace and retain E + M. WHIR consumes M
    /// after batching retires E; keeping full cosets is not a valid choice here.
    RetainMonomials {
        whir: OpeningPolicy,
    },
    /// Commit through the raw backing, then restore its evaluations before
    /// GKR. WHIR may regenerate into full, retained-M, or in-place storage.
    InPlace {
        whir: OpeningPolicy,
    },
}

impl Default for WitnessMemoryPolicy {
    fn default() -> Self {
        Self::FullMaterialization {
            whir: FullWitnessWhirPolicy::RetainCosets,
        }
    }
}

/// Setup and memory open separately at query time.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProofMemoryPolicy {
    pub setup: OpeningPolicy,
    pub memory: OpeningPolicy,
    pub witness: WitnessMemoryPolicy,
}

impl ProofMemoryPolicy {
    pub fn candidates() -> impl Iterator<Item = Self> {
        const OPENINGS: [OpeningPolicy; 3] = [
            OpeningPolicy::FullMaterialization,
            OpeningPolicy::RetainMonomials,
            OpeningPolicy::InPlace,
        ];
        let witnesses = std::iter::once(WitnessMemoryPolicy::default())
            .chain(
                OPENINGS.map(|whir| WitnessMemoryPolicy::FullMaterialization {
                    whir: FullWitnessWhirPolicy::Recompute(whir),
                }),
            )
            .chain(OPENINGS.map(|whir| WitnessMemoryPolicy::RetainMonomials { whir }))
            .chain(OPENINGS.map(|whir| WitnessMemoryPolicy::InPlace { whir }));
        OPENINGS.into_iter().flat_map(move |setup| {
            let witnesses = witnesses.clone();
            OPENINGS.into_iter().flat_map(move |memory| {
                witnesses.clone().map(move |witness| Self {
                    setup,
                    memory,
                    witness,
                })
            })
        })
    }
}
