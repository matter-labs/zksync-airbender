//! Shared verifier logic compiled under both `security_80` and `security_100`.
//
// Note:
// Each security module mounts this directory through `#[path = "../shared/mod.rs"]`.
// The parent security module provides the security-specific `concrete` module and
// the common verifier imports, while this shared layer reuses the verifier logic
// through module scoping. We intentionally keep the security split at the module
// boundary instead of threading it through const generics, because the const-generic
// version would make this verifier substantially more verbose without improving the
// generated code or the reviewability of this migration.

// Note: these `use`s are needed for the declared modules to work, they are accessed
// via `use super::<...>` there, and `super` here is either `security_80` or
// `security_100`.
use super::concrete;
use super::concrete::*;
use super::*;

mod implementation;
mod skeleton;
mod utils;

#[cfg(test)]
mod tests;

pub(crate) use self::skeleton::{ProofSkeleton, QueryValues};
use self::utils::*;

pub use self::implementation::{
    verify, verify_with_configuration, ConcreteProofOutput, ConcreteProofPublicInputs,
};
