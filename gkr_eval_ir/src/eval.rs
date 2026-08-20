//! Row-bound reference evaluator for the canonical DAG IR.

use std::collections::HashMap;

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};

use crate::{
    ChallengeRef, DagLayer, Expr, ExprId, LookupValueKind, ReadPlace, RootId, SourceKind,
    VirtualSetupKind,
};

pub type Bf = BabyBearField;
pub type Ext = BabyBearExt4;

#[inline(always)]
fn lift(value: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(value)
}

pub trait ReadResolver {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext;
}

pub trait LookupResolver {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf;
}

pub trait VirtualSetupResolver {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf;

    fn virtual_setup_fold(&self, kind: &VirtualSetupKind, y: usize, challenges: &[Ext]) -> Ext {
        fold_vs_from_originals(&|z| lift(self.virtual_setup(kind, z)), y, challenges)
    }
}

pub fn fold_vs_from_originals(base: &dyn Fn(usize) -> Ext, y: usize, challenges: &[Ext]) -> Ext {
    match challenges.split_last() {
        None => base(y),
        Some((challenge, rest)) => {
            let a = fold_vs_from_originals(base, 2 * y, rest);
            let b = fold_vs_from_originals(base, 2 * y + 1, rest);
            let mut delta = b;
            delta.sub_assign(&a);
            delta.mul_assign(challenge);
            let mut result = a;
            result.add_assign(&delta);
            result
        }
    }
}

pub trait ChallengeResolver {
    fn challenge(&self, reference: &ChallengeRef) -> Ext;
}

pub struct Resolvers<'a> {
    pub read: &'a dyn ReadResolver,
    pub lookup: &'a dyn LookupResolver,
    pub virtual_setup: &'a dyn VirtualSetupResolver,
    pub challenge: &'a dyn ChallengeResolver,
}

pub fn eval_layer_root(layer: &DagLayer, root: RootId, row: usize, r: &Resolvers<'_>) -> Ext {
    let mut cache = HashMap::new();
    eval_expr(layer.roots[root.0 as usize].expr, layer, row, r, &mut cache)
}

pub fn eval_layer_expr(layer: &DagLayer, expr: ExprId, row: usize, r: &Resolvers<'_>) -> Ext {
    let mut cache = HashMap::new();
    eval_expr(expr, layer, row, r, &mut cache)
}

fn eval_expr(
    id: ExprId,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(value) = cache.get(&id) {
        return *value;
    }
    let value = match &layer.exprs[id.0 as usize] {
        Expr::Source(source) => {
            eval_source(&layer.sources[source.0 as usize], layer, row, r, cache)
        }
        Expr::Add(terms) => {
            let mut result = Ext::ZERO;
            for term in terms {
                result.add_assign(&eval_expr(*term, layer, row, r, cache));
            }
            result
        }
        Expr::Mul(factors) => {
            let mut result = Ext::ONE;
            for factor in factors {
                result.mul_assign(&eval_expr(*factor, layer, row, r, cache));
            }
            result
        }
    };
    cache.insert(id, value);
    value
}

fn eval_source(
    kind: &SourceKind,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    match kind {
        SourceKind::Constant { value } => lift(Bf::from_u32_with_reduction(*value)),
        SourceKind::Challenge { reference } => r.challenge.challenge(reference),
        SourceKind::Read { place } => r.read.read(place, row),
        SourceKind::VirtualSetup { kind } => lift(r.virtual_setup.virtual_setup(kind, row)),
        SourceKind::InitsAndTeardownsTopBits { reference } => lift(Bf::from_u32_with_reduction(
            (reference.set_index as u32)
                .checked_shl(reference.shift)
                .unwrap_or(0),
        )),
        SourceKind::LookupValue {
            kind,
            set_index,
            query,
        } => {
            let query = eval_expr(*query, layer, row, r, cache);
            lift(r.lookup.lookup(kind, *set_index, query, row))
        }
    }
}
