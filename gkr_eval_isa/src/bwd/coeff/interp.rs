//! Scalar semantic interpreter for the coefficient IR (design §4).
//!
//! One row in, `(acc_c0, acc_c2)` out. There is no `T0`/`T2` role, no generic
//! arithmetic accumulator, and no `acc_c1`: the round update recovers `c1` from
//! the normalized claim. This is the CPU semantic reference the GPU program is
//! validated against — it deliberately knows nothing about cells, moves, paging,
//! or the wire encoding.

use cs::gkr_compiler::dag_ir::Ext;
use field::Field;

use super::model::{
    CoeffError, CoeffLayer, CoeffTerm, CoefficientRecipeId, Projection, ProjectionId, SourceId,
    TermId,
};

/// The two values a coefficient program needs from its environment.
///
/// [`CoeffResolver::coefficient`] is only ever called for a BANKED id: reserved
/// literals (`+1`/`-1`) are resolved by the interpreter itself, so an
/// implementation never has to allocate an evaluated bank entry for them.
///
/// [`CoeffResolver::source_pair`] returns the source's two named projections at
/// `row`, in that order: `(Endpoint0, Delta) = (s0, s1 - s0)`. It is a PAIR
/// because a native dual factor performs one physical source-pair resolution, not
/// two projection reads (§8).
pub trait CoeffResolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext;
    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext);
}

/// Interpret one row of `layer`, returning `(acc_c0, acc_c2)`.
///
/// `acc_c0` starts at the per-thread `c_init` initializer (or zero when the layer
/// has none) and `acc_c2` at zero; every term then adds its own contribution:
///
/// ```text
/// C0Linear(k, a0)        acc_c0 += k * a0
/// C2Product(k, da, db)   acc_c2 += k * da * db
/// DualProduct(k, A, B)   acc_c0 += k * A.s0 * B.s0 ; acc_c2 += k * A.ds * B.ds
/// ```
pub fn interpret_coeff_layer(
    layer: &CoeffLayer,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    let mut acc_c0 = match layer.c_init {
        Some(id) => coefficient(layer, id, resolver)?,
        None => Ext::ZERO,
    };
    let mut acc_c2 = Ext::ZERO;

    for term in &layer.terms {
        let k = coefficient(layer, term.coefficient(), resolver)?;
        match term {
            CoeffTerm::C0Linear { id, value, .. } => {
                let (e0, _) = projection(layer, *id, *value, Projection::Endpoint0, row, resolver)?;
                let mut v = k;
                v.mul_assign(&e0);
                acc_c0.add_assign(&v);
            }
            CoeffTerm::C2Product { id, lhs, rhs, .. } => {
                let (_, dl) = projection(layer, *id, *lhs, Projection::Delta, row, resolver)?;
                let (_, dr) = projection(layer, *id, *rhs, Projection::Delta, row, resolver)?;
                let mut v = k;
                v.mul_assign(&dl);
                v.mul_assign(&dr);
                acc_c2.add_assign(&v);
            }
            CoeffTerm::DualProduct { lhs, rhs, .. } => {
                let (l0, ld) = source_pair(layer, *lhs, row, resolver)?;
                let (r0, rd) = source_pair(layer, *rhs, row, resolver)?;
                let mut c0 = k;
                c0.mul_assign(&l0);
                c0.mul_assign(&r0);
                acc_c0.add_assign(&c0);
                let mut c2 = k;
                c2.mul_assign(&ld);
                c2.mul_assign(&rd);
                acc_c2.add_assign(&c2);
            }
        }
    }
    Ok((acc_c0, acc_c2))
}

/// Reserved literals resolve internally (no bank entry, no resolver call); every
/// other id is validated against the bank before the resolver is asked. A banked
/// zero recipe is a compiler error, so it is rejected rather than evaluated.
fn coefficient(
    layer: &CoeffLayer,
    id: CoefficientRecipeId,
    resolver: &impl CoeffResolver,
) -> Result<Ext, CoeffError> {
    if let Some(v) = id.literal() {
        return Ok(v);
    }
    match layer.banked_recipe(id) {
        None => Err(CoeffError::UnknownCoefficient { id }),
        Some(r) if r.is_zero() => Err(CoeffError::EncodedZeroCoefficient { id }),
        Some(_) => Ok(resolver.coefficient(id)),
    }
}

fn source_pair(
    layer: &CoeffLayer,
    id: SourceId,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    if layer.source(id).is_none() {
        return Err(CoeffError::UnknownSource { id });
    }
    Ok(resolver.source_pair(id, row))
}

/// Resolve a projection, rejecting a role its opcode cannot consume.
fn projection(
    layer: &CoeffLayer,
    term: TermId,
    p: ProjectionId,
    expected: Projection,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    if p.projection != expected {
        return Err(CoeffError::ProjectionRoleMismatch { term, expected, found: p.projection });
    }
    source_pair(layer, p.source, row, resolver)
}
