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
