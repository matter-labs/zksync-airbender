pub(crate) mod distill;
pub(crate) mod fragment;
pub(crate) mod group;
pub(crate) mod interp;
pub(crate) mod lean;
pub(crate) mod lean_bind;
pub(crate) mod limits;
pub(crate) mod lower;
pub(crate) mod model;
pub(crate) mod order;
pub(crate) mod source;
pub(crate) mod source_layout;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BwdRegime {
    R0,
    Ext,
}
