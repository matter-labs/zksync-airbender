use super::queries::*;
use super::*;
use crate::gkr::prover_config::WhirSchedule;
use crate::merkle_trees::MerkleTreeCapVarLength;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(bound = "")]
pub struct WhirCommitment<F: PrimeField, T: ColumnMajorMerkleTreeConstructor<F>> {
    pub cap: MerkleTreeCapVarLength,
    pub _marker: core::marker::PhantomData<(F, T)>,
}

impl<F: PrimeField, T: ColumnMajorMerkleTreeConstructor<F>> Default for WhirCommitment<F, T> {
    fn default() -> Self {
        Self {
            cap: MerkleTreeCapVarLength::default(),
            _marker: core::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, T: ColumnMajorMerkleTreeConstructor<F>> WhirCommitment<F, T> {
    pub fn estimate_size(&self) -> usize {
        self.cap.estimate_size()
    }
}

/// One base oracle (memory, witness or setup tree): its cap, the claims of
/// its committed (packed) columns at the WHIR claim point and its round-0
/// query openings.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, E: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct WhirBaseLayerCommitmentAndQueries<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub commitment: WhirCommitment<F, T>,
    pub num_columns: usize,
    pub evals: Vec<E>, // num_columns
    pub queries: Vec<BaseFieldQuery<F, T>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
    WhirBaseLayerCommitmentAndQueries<F, E, T>
{
    pub fn estimate_size(&self) -> usize {
        self.commitment.estimate_size()
            + self.evals.len() * E::DEGREE * core::mem::size_of::<u32>()
            + self.queries.len()
                * self
                    .queries
                    .first()
                    .map(|el| el.estimate_size())
                    .unwrap_or(0)
    }
}

/// One committed intermediate oracle together with everything the round that
/// consumes it puts into the transcript, in transcript order: right after the
/// commitment its OOD sample(s) (PoW nonce, if the OOD draw is gated, then
/// the claimed evaluations); then — in the NEXT round — the sumcheck
/// polynomials folding it (with one PoW nonce per folding challenge when the
/// folding draws are gated), the query-draw PoW nonce and the query openings.
/// See [`WhirInternalRound`](crate::gkr::prover_config::WhirInternalRound)
/// for the schedule knobs these mirror.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, E: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct WhirIntermediateCommitmentAndQueries<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub commitment: WhirCommitment<F, T>,
    /// PoW nonce gating this oracle's OOD point draw; present iff the
    /// round's `ood_pow_bits > 0`.
    #[serde(default)]
    pub ood_pow_nonce: Option<u64>,
    /// The `num_ood_samples` out-of-domain evaluations of this oracle's
    /// polynomial, in draw order.
    #[serde(default)]
    pub ood_samples: Vec<E>,
    /// The `folding_log2` degree-2 sumcheck round polynomials (as `[s(0),
    /// s(1), s(1/2)]`-interpolated monomial coefficients) folding this
    /// oracle's polynomial.
    #[serde(default)]
    pub sumcheck_polys: Vec<[E; 3]>,
    /// One PoW nonce per folding-challenge draw iff the round's
    /// `folding_pow_bits > 0`; empty otherwise.
    #[serde(default)]
    pub folding_pow_nonces: Vec<u64>,
    /// PoW nonce gating the query-index draw into this oracle.
    #[serde(default)]
    pub queries_pow_nonce: u64,
    pub queries: Vec<ExtensionFieldQuery<F, E, T>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
    WhirIntermediateCommitmentAndQueries<F, E, T>
{
    /// A freshly committed oracle: the cap only, everything else is filled
    /// as the transcript proceeds.
    pub fn with_commitment(cap: MerkleTreeCapVarLength) -> Self {
        Self {
            commitment: WhirCommitment {
                cap,
                _marker: core::marker::PhantomData,
            },
            ood_pow_nonce: None,
            ood_samples: vec![],
            sumcheck_polys: vec![],
            folding_pow_nonces: vec![],
            queries_pow_nonce: 0,
            queries: vec![],
        }
    }

    pub fn estimate_size(&self) -> usize {
        self.commitment.estimate_size()
            + self
                .ood_pow_nonce
                .map_or(0, |_| core::mem::size_of::<u64>())
            + self.ood_samples.len() * E::DEGREE * core::mem::size_of::<u32>()
            + self.sumcheck_polys.len() * 3 * E::DEGREE * core::mem::size_of::<u32>()
            + self.folding_pow_nonces.len() * core::mem::size_of::<u64>()
            + core::mem::size_of::<u64>()
            + self.queries.len()
                * self
                    .queries
                    .first()
                    .map(|el| el.estimate_size())
                    .unwrap_or(0)
    }
}

/// The WHIR part of a GKR proof, in transcript order: the base-oracle caps
/// and claims (the caps enter the transcript at commitment time, the claims
/// come out of the GKR phase), the batching-challenge PoW nonce, the round-0
/// sumcheck (explicit packing only), intermediate oracle 0 with its OOD
/// samples, the round-0 query PoW nonce and base-oracle openings, then every
/// further intermediate oracle, and finally the plain-text tail polynomial.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, E: serde::Serialize + serde::de::DeserializeOwned"
)]
#[serde(from = "legacy_compat::WhirPolyCommitProofRepr<F, E, T>")]
pub struct WhirPolyCommitProof<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub setup_commitment: WhirBaseLayerCommitmentAndQueries<F, E, T>,
    pub memory_commitment: WhirBaseLayerCommitmentAndQueries<F, E, T>,
    pub witness_commitment: WhirBaseLayerCommitmentAndQueries<F, E, T>,
    /// PoW nonce gating the batching-challenge draw: the batched-proximity
    /// PoW under explicit packing, the initial-folding PoW under virtual
    /// packing (where the batching challenge IS the `2^k`-ary fold of the
    /// virtual packed polynomial).
    pub batching_challenge_pow_nonce: u64,
    /// Round-0 sumcheck polynomials: `folding_log2` of them under explicit
    /// packing, none under virtual packing.
    pub base_sumcheck_polys: Vec<[E; 3]>,
    /// One PoW nonce per round-0 folding-challenge draw iff the base round's
    /// `folding_pow_bits > 0`; empty otherwise.
    pub base_folding_pow_nonces: Vec<u64>,
    /// PoW nonce gating the round-0 query-index draw into the base oracles.
    pub base_queries_pow_nonce: u64,
    pub intermediate_whir_oracles: Vec<WhirIntermediateCommitmentAndQueries<F, E, T>>,
    pub final_monomials: Vec<E>,
    pub whir_schedule: WhirSchedule,
}

impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
    WhirPolyCommitProof<F, E, T>
{
    pub fn estimate_size(&self) -> usize {
        self.setup_commitment.estimate_size()
            + self.memory_commitment.estimate_size()
            + self.witness_commitment.estimate_size()
            + core::mem::size_of::<u64>()
            + self.base_sumcheck_polys.len() * 3 * E::DEGREE * core::mem::size_of::<u32>()
            + self.base_folding_pow_nonces.len() * core::mem::size_of::<u64>()
            + core::mem::size_of::<u64>()
            + self
                .intermediate_whir_oracles
                .iter()
                .map(|el| el.estimate_size())
                .sum::<usize>()
            + self.final_monomials.len() * E::DEGREE * core::mem::size_of::<u32>()
    }

    /// Every sumcheck round polynomial in transcript order: the base round's,
    /// then each intermediate oracle's.
    pub fn all_sumcheck_polys(&self) -> impl Iterator<Item = &[E; 3]> {
        self.base_sumcheck_polys.iter().chain(
            self.intermediate_whir_oracles
                .iter()
                .flat_map(|o| o.sumcheck_polys.iter()),
        )
    }

    /// Every OOD sample in transcript order.
    pub fn all_ood_samples(&self) -> impl Iterator<Item = &E> {
        self.intermediate_whir_oracles
            .iter()
            .flat_map(|o| o.ood_samples.iter())
    }

    /// The query-draw PoW nonces per round: the base round's, then each
    /// intermediate oracle's.
    pub fn queries_pow_nonces(&self) -> Vec<u64> {
        core::iter::once(self.base_queries_pow_nonce)
            .chain(
                self.intermediate_whir_oracles
                    .iter()
                    .map(|o| o.queries_pow_nonce),
            )
            .collect()
    }
}

// LEGACY-COMPAT (delete once every tracked proof fixture has been regenerated
// with the refactored layout): the pre-refactor serialized `WhirPolyCommitProof`
// carried the per-round data as flat vectors — `sumcheck_polys` (every
// round's, concatenated), `ood_samples` (one per intermediate oracle) and
// `pow_nonces` (one query-draw nonce per round) — plus GKR->WHIR handoff
// values. The decoder accepts both layouts; the batching-challenge nonce of a
// legacy proof lived on the enclosing `GKRProof`, whose decoder re-attaches it.
pub(crate) mod legacy_compat {
    use super::*;

    #[derive(serde::Deserialize)]
    #[serde(
        bound = "F: serde::Serialize + serde::de::DeserializeOwned, E: serde::Serialize + serde::de::DeserializeOwned"
    )]
    pub(crate) struct WhirPolyCommitProofRepr<
        F: PrimeField,
        E: FieldExtension<F> + Field,
        T: ColumnMajorMerkleTreeConstructor<F>,
    > {
        setup_commitment: WhirBaseLayerCommitmentAndQueries<F, E, T>,
        memory_commitment: WhirBaseLayerCommitmentAndQueries<F, E, T>,
        witness_commitment: WhirBaseLayerCommitmentAndQueries<F, E, T>,
        intermediate_whir_oracles: Vec<WhirIntermediateCommitmentAndQueries<F, E, T>>,
        final_monomials: Vec<E>,
        whir_schedule: WhirSchedule,
        // current layout
        #[serde(default)]
        batching_challenge_pow_nonce: Option<u64>,
        #[serde(default)]
        base_sumcheck_polys: Option<Vec<[E; 3]>>,
        #[serde(default)]
        base_folding_pow_nonces: Option<Vec<u64>>,
        #[serde(default)]
        base_queries_pow_nonce: Option<u64>,
        // legacy layout
        #[serde(default)]
        ood_samples: Option<Vec<E>>,
        #[serde(default)]
        sumcheck_polys: Option<Vec<[E; 3]>>,
        #[serde(default)]
        pow_nonces: Option<Vec<u64>>,
    }

    impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
        From<WhirPolyCommitProofRepr<F, E, T>> for WhirPolyCommitProof<F, E, T>
    {
        fn from(repr: WhirPolyCommitProofRepr<F, E, T>) -> Self {
            let mut intermediate_whir_oracles = repr.intermediate_whir_oracles;
            let whir_schedule = repr.whir_schedule;
            let (
                batching_challenge_pow_nonce,
                base_sumcheck_polys,
                base_folding_pow_nonces,
                base_queries_pow_nonce,
            ) = match (repr.pow_nonces, repr.sumcheck_polys, repr.ood_samples) {
                (None, None, None) => (
                    repr.batching_challenge_pow_nonce
                        .expect("WHIR proof: batching_challenge_pow_nonce"),
                    repr.base_sumcheck_polys
                        .expect("WHIR proof: base_sumcheck_polys"),
                    repr.base_folding_pow_nonces.unwrap_or_default(),
                    repr.base_queries_pow_nonce
                        .expect("WHIR proof: base_queries_pow_nonce"),
                ),
                (Some(pow_nonces), Some(sumcheck_polys), Some(ood_samples)) => {
                    let fold_steps = whir_schedule.fold_steps();
                    let num_rounds = fold_steps.len();
                    assert_eq!(
                        pow_nonces.len(),
                        num_rounds,
                        "legacy WHIR proof: pow_nonces"
                    );
                    assert_eq!(
                        intermediate_whir_oracles.len(),
                        num_rounds - 1,
                        "legacy WHIR proof: intermediate oracles"
                    );
                    assert_eq!(
                        ood_samples.len(),
                        num_rounds - 1,
                        "legacy WHIR proof: one OOD sample per intermediate oracle"
                    );
                    assert_eq!(
                        sumcheck_polys.len(),
                        fold_steps.iter().sum::<usize>(),
                        "legacy WHIR proof: sumcheck_polys"
                    );
                    let mut polys = sumcheck_polys.into_iter();
                    let base_sumcheck_polys: Vec<[E; 3]> =
                        polys.by_ref().take(fold_steps[0]).collect();
                    for (i, oracle) in intermediate_whir_oracles.iter_mut().enumerate() {
                        oracle.ood_samples = vec![ood_samples[i]];
                        oracle.sumcheck_polys = polys.by_ref().take(fold_steps[i + 1]).collect();
                        oracle.queries_pow_nonce = pow_nonces[i + 1];
                    }
                    // the batching nonce of a legacy proof lives on the
                    // enclosing GKRProof; its decoder fills it in
                    (0, base_sumcheck_polys, vec![], pow_nonces[0])
                }
                _ => panic!("WHIR proof JSON mixes the current and the legacy layout"),
            };
            Self {
                setup_commitment: repr.setup_commitment,
                memory_commitment: repr.memory_commitment,
                witness_commitment: repr.witness_commitment,
                batching_challenge_pow_nonce,
                base_sumcheck_polys,
                base_folding_pow_nonces,
                base_queries_pow_nonce,
                intermediate_whir_oracles,
                final_monomials: repr.final_monomials,
                whir_schedule,
            }
        }
    }
}
