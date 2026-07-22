#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

pub mod field_wrapper;
pub use self::field_wrapper::*;

pub mod gkr;
pub mod utils;
pub mod whir;

/// Curated inner-attribute header prepended to the root of every generated
/// verifier module (`<circuit>/<level>/mod.rs` and the shared `common/mod.rs`).
///
/// The verifier code in `verifier/src/generated/**` is machine-emitted by this
/// crate, so it legitimately cannot satisfy a set of stylistic / structural
/// lints that assume hand-written code. Rather than a blanket
/// `#![allow(warnings)]`, we allow exactly the lints that machine emission
/// provokes, each justified below, so real regressions in the generator still
/// surface as warnings. As an inner attribute at a module root, each entry
/// propagates to that module and all of its descendant modules (`constants`,
/// `gkr`, `whir`, `common`).
///
/// Justifications (all inherent to uniform code generation, not hand-fixable in
/// the generated output):
/// - `clippy::needless_range_loop`: emitted loops index fixed-size arrays by
///   position; the index is structural, not incidental.
/// - `clippy::too_many_arguments`: generated verify/fold signatures thread all
///   circuit parameters explicitly; arity is dictated by the circuit.
/// - `clippy::missing_safety_doc`: generated `unsafe fn`s have no prose docs.
/// - `clippy::manual_div_ceil` / `clippy::identity_op` /
///   `clippy::large_const_arrays`: constant sizing arithmetic and const tables
///   are emitted in canonical unfolded form (e.g. `(n + 15) / 16`, `x * 1`).
/// - `clippy::borrow_deref_ref`: uniform `&*expr` reborrows in emitted call
///   sites.
/// - `clippy::duplicate_mod`: the single shared `common/mod.rs` is
///   `#[path]`-included by every per-circuit module by design (each circuit
///   gets its own monomorphized `common`), so it is loaded as a module many
///   times; this is intentional source sharing, not accidental duplication.
/// - `unused_imports`: the generator emits a uniform `use` preamble in each
///   `gkr.rs` / `constants.rs`, but which imported symbols a given circuit
///   actually references is circuit-dependent. Some are trait imports (e.g.
///   `FieldExtension`) that count as used only when one of the trait's methods
///   is called, so usage cannot be determined textually; others are constants
///   (`BLAKE2S_*`) exercised by most circuits but not all (e.g.
///   `inits_and_teardowns`). Pruning per file would require threading
///   per-circuit symbol/method-usage analysis through codegen — a structural
///   change — so this lint stays allowed. (Note: `unused_assignments` is NOT
///   allowed; its single dead-store emission site was fixed at the source.)
/// - `unused_unsafe`, plus `dead_code` / `unused_variables` / `unused_mut`
///   guarded against circuit-to-circuit emission drift: the generator emits
///   uniform `unsafe` and binding scaffolding regardless of whether a given
///   circuit exercises every step.
pub fn generated_lint_allow_header() -> proc_macro2::TokenStream {
    quote::quote! {
        #![allow(
            clippy::needless_range_loop,
            clippy::too_many_arguments,
            clippy::missing_safety_doc,
            clippy::manual_div_ceil,
            clippy::identity_op,
            clippy::large_const_arrays,
            clippy::borrow_deref_ref,
            clippy::duplicate_mod,
            unused_imports,
            unused_unsafe,
            dead_code,
            unused_variables,
            unused_mut
        )]
    }
}
