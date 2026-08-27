use super::*;
use field::PrimeField;

pub const DECODER_LOOKUP_FORMAL_SET_INDEX: usize = usize::MAX;

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SingleColumnLookupRelation<F: PrimeField> {
    pub input: LinearRelation<F>,
    // index of the lookup set for the witness generation mapping, so we can just peek in there instead of evaluating
    // the relation again
    pub lookup_set_index: usize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VectorLookupRelation<F: PrimeField> {
    pub columns: Box<[LinearRelation<F>]>,
    // index of the lookup set for the witness generation mapping, so we can just peek in there instead of evaluating
    // the relation again
    pub lookup_set_index: usize,
}
