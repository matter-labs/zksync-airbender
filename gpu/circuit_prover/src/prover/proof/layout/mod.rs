//! gkr-dependent builder for the device-resident proof image.
//!
//! The proof-image layout TYPES (slab byte ranges + typed accessors) live one
//! layer down in [`crate::prover::proof_layout`], which depends only on
//! `primitives` + `upstream`. This module hosts the BUILDER that *derives*
//! those inputs from a compiled circuit + WHIR schedule + base-layer
//! geometries — it calls into `gkr::transform` and `gkr::backward`, so it must
//! sit above `gkr` in the module DAG (and therefore cannot live in the
//! cycle-free `proof_layout` leaf).

mod build_inputs;
pub(crate) use build_inputs::build_proof_layout_inputs;
