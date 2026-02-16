use super::queries::*;
use super::*;
use crate::merkle_trees::MerkleTreeCapVarLength;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct WhirIntermediateCommitmentAndQueries<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub commitment: WhirCommitment<F, T>,
    pub queries: Vec<ExtensionFieldQuery<F, E, T>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
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
}
