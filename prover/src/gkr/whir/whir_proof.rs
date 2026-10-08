use super::queries::*;
use super::*;
use crate::gkr::prover::WhirSchedule;
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
    pub queries: Vec<ExtensionFieldQuery<F, E, T>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
    WhirIntermediateCommitmentAndQueries<F, E, T>
{
    pub fn estimate_size(&self) -> usize {
        self.commitment.estimate_size()
            + self.queries.len()
                * self
                    .queries
                    .first()
                    .map(|el| el.estimate_size())
                    .unwrap_or(0)
    }
}

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
    pub intermediate_whir_oracles: Vec<WhirIntermediateCommitmentAndQueries<F, E, T>>,
    pub ood_samples: Vec<E>,
    pub sumcheck_polys: Vec<[E; 3]>,
    pub pow_nonces: Vec<u64>,
    pub final_monomials: Vec<E>,
    pub whir_schedule: WhirSchedule,
    // GKR->WHIR handoff values the prover records so a verifier-calldata serializer can build the
    // committed-state preimage without replaying the GKR transcript (optional for back-compat with
    // proofs serialized before these fields existed).
    #[serde(default)]
    pub batching_challenge: Option<E>,
    #[serde(default)]
    pub original_evaluation_point: Option<Vec<E>>,
    #[serde(default)]
    pub batched_opening: Option<E>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field, T: ColumnMajorMerkleTreeConstructor<F>>
    WhirPolyCommitProof<F, E, T>
{
    pub fn estimate_size(&self) -> usize {
        self.setup_commitment.estimate_size()
            + self.memory_commitment.estimate_size()
            + self.witness_commitment.estimate_size()
            + self
                .intermediate_whir_oracles
                .iter()
                .map(|el| el.estimate_size())
                .sum::<usize>()
            + self.ood_samples.len() * E::DEGREE * core::mem::size_of::<u32>()
            + self.sumcheck_polys.len() * 3 * E::DEGREE * core::mem::size_of::<u32>()
            + self.pow_nonces.len() * core::mem::size_of::<u64>()
            + self.final_monomials.len() * E::DEGREE * core::mem::size_of::<u32>()
    }
}
