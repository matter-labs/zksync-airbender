//! Forward VM compiler and 16-bit-lane encoding for `gkr_eval_ir`.
pub(crate) mod artifact;
pub(crate) mod binding;
pub(crate) mod compile;
pub(crate) mod context;
pub(crate) mod encode;
pub(crate) mod error;
pub(crate) mod isa;
#[cfg(feature = "search")]
pub(crate) mod search;
pub(crate) mod source;
pub(crate) mod stats;
pub(crate) mod validate;

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum FieldTag {
    #[serde(rename = "proth120")]
    Proth120,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ElementModel {
    pub bf_lanes_per_bucket: u32,
    pub constant_width: u32,
    pub minus_one: u128,
    pub field: Option<FieldTag>,
}

impl ElementModel {
    pub const BABYBEAR: Self = Self {
        bf_lanes_per_bucket: 4,
        constant_width: 4,
        minus_one: 2_013_265_920,
        field: None,
    };

    pub const PROTH120: Self = Self {
        bf_lanes_per_bucket: 1,
        constant_width: 16,
        minus_one: <field::proth120::Proth120 as field::PrimeField>::CHARACTERISTICS_U128 - 1,
        field: Some(FieldTag::Proth120),
    };

    pub fn for_dag(dag: &gkr_eval_ir::DagCircuit) -> Self {
        match dag.modulus {
            modulus if modulus == Self::BABYBEAR.minus_one + 1 => Self::BABYBEAR,
            modulus if modulus == Self::PROTH120.minus_one + 1 => Self::PROTH120,
            modulus => panic!("ElementModel: unsupported DAG modulus {modulus}"),
        }
    }
}
