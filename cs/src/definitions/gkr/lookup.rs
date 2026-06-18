use super::*;

pub const DECODER_LOOKUP_FORMAL_SET_INDEX: usize = usize::MAX;

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldSingleColumnLookupRelation {
    pub input: NoFieldLinearRelation,
    // index of the lookup set for the witness generation mapping, so we can just peek in there instead of evaluating
    // the relation again
    pub lookup_set_index: usize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldVectorLookupRelation {
    pub columns: Box<[NoFieldLinearRelation]>,
    // index of the lookup set for the witness generation mapping, so we can just peek in there instead of evaluating
    // the relation again
    pub lookup_set_index: usize,
}
