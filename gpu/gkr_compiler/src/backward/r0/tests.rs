use super::*;
use crate::backward::{
    CoeffLayer, CoefficientRecipeId, NormalizedCoefficientRecipe, WindowCoefficientPlan,
};

struct LoweredLayer {
    window: WindowProgram,
    scalar_seed: Option<u16>,
    coefficients: CoeffLayer,
}

fn compile_lowering(dag: &DagCircuit, tails: bool) -> Result<Vec<LoweredLayer>, R0CompileError> {
    let fields = crate::analysis::build_cross_layer_field_map(dag);
    dag.layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| {
            let program = crate::backward::r0::compile_layer(layer, canonical, &fields)?;
            let (window, scalar_seed) = lower_r0_window_program(&program, tails)
                .map_err(|error| R0CompileError::Window { layer, error })?;
            Ok(LoweredLayer {
                window,
                scalar_seed,
                coefficients: program.coefficients,
            })
        })
        .collect()
}

fn c_init_recipe(coefficients: &CoeffLayer) -> Option<NormalizedCoefficientRecipe> {
    coefficients.c_init.map(|id| match id {
        CoefficientRecipeId::ONE => NormalizedCoefficientRecipe::one(),
        CoefficientRecipeId::NEG_ONE => NormalizedCoefficientRecipe::neg_one(),
        _ => coefficients.coefficients[id.bank_index().unwrap()].clone(),
    })
}

use crate::backward::common::model::CoeffTerm;
use crate::backward::common::source::OriginLeaf;
use crate::backward::common::{Bf, Ext};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_ir::{ChallengePower, Expr, SourceKind};

fn lift(v: u32) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(v))
}
fn symbol(key: impl core::fmt::Debug, salt: usize) -> Ext {
    let mut h = (salt as u32).wrapping_add(19);
    for b in format!("{key:?}").bytes() {
        h = h.wrapping_mul(16777619) ^ u32::from(b);
    }
    use field::baby_bear::ext2::BabyBearExt2;
    Ext::new(
        BabyBearExt2::new(
            Bf::from_u32_with_reduction(h),
            Bf::from_u32_with_reduction(h.wrapping_add(29)),
        ),
        BabyBearExt2::new(
            Bf::from_u32_with_reduction(h.wrapping_mul(3)),
            Bf::from_u32_with_reduction(h.wrapping_add(71)),
        ),
    )
}
fn challenge(r: gkr_eval_ir::ChallengeRef) -> Ext {
    symbol(r.key, 101).pow(match r.power {
        ChallengePower::One => 1,
        ChallengePower::Static(n) => n,
    })
}
fn recipe(r: &NormalizedCoefficientRecipe) -> Ext {
    let mut sum = Ext::ZERO;
    for term in &r.terms {
        let mut v = lift(term.scalar);
        for c in &term.challenges {
            v.mul_assign(&challenge(c.0));
        }
        for r in &term.inits_and_teardowns_top_bits {
            v.mul_assign(&lift(((r.set_index as u32 + 1) >> (r.shift % 8)) & 1));
        }
        sum.add_assign(&v);
    }
    sum
}
fn coefficient(c: &CoeffLayer, id: super::super::CoefficientRecipeId) -> Ext {
    id.literal()
        .unwrap_or_else(|| recipe(&c.coefficients[id.bank_index().unwrap()]))
}
fn leaf(origin: &OriginLeaf, row: usize, x: Ext) -> Ext {
    let a = symbol(origin, row * 2);
    let mut delta = symbol(origin, row * 2 + 1);
    delta.sub_assign(&a);
    delta.mul_assign(&x);
    delta.add_assign(&a);
    delta
}
fn expression(d: &gkr_eval_ir::DagLayer, row: usize, x: Ext) -> Ext {
    let mut values = Vec::<Ext>::new();
    for expr in &d.exprs {
        let v = match expr {
            Expr::Source(s) => match &d.sources[s.0 as usize] {
                SourceKind::Read { place } => leaf(&OriginLeaf::Read(*place), row, x),
                SourceKind::VirtualSetup { kind } => {
                    leaf(&OriginLeaf::VirtualSetup { kind: *kind }, row, x)
                }
                SourceKind::Constant { value } => lift(*value),
                SourceKind::Challenge { reference } => challenge(*reference),
                SourceKind::InitsAndTeardownsTopBits { reference: r } => {
                    lift(((r.set_index as u32 + 1) >> (r.shift % 8)) & 1)
                }
                SourceKind::LookupValue { .. } => {
                    panic!("distillation must erase lookup leaves")
                }
            },
            Expr::Add(children) => {
                let mut v = Ext::ZERO;
                for e in children {
                    v.add_assign(&values[e.0 as usize]);
                }
                v
            }
            Expr::Mul(children) => {
                let mut v = Ext::ONE;
                for e in children {
                    v.mul_assign(&values[e.0 as usize]);
                }
                v
            }
        };
        values.push(v);
    }
    values[d.roots[0].expr.0 as usize]
}
fn expanded(c: &CoeffLayer, row: usize, x: Ext) -> Ext {
    let mut value = c.c_init.map_or(Ext::ZERO, |id| coefficient(c, id));
    for term in &c.terms {
        let (id, mut v) = match term {
            CoeffTerm::C0Linear {
                coefficient, value, ..
            } => (
                *coefficient,
                leaf(&c.sources[value.source.0 as usize].origin, row, x),
            ),
            CoeffTerm::C2Product {
                coefficient,
                lhs,
                rhs,
                ..
            } => {
                let mut v = leaf(&c.sources[lhs.source.0 as usize].origin, row, x);
                v.mul_assign(&leaf(&c.sources[rhs.source.0 as usize].origin, row, x));
                (*coefficient, v)
            }
            _ => panic!("recomputation retains the R0 wire classes"),
        };
        v.mul_assign(&coefficient(c, id));
        value.add_assign(&v);
    }
    value
}

#[test]
fn cpu_r0_matches_expression_corpus() {
    let dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let mut layers = 0;
    let mut expected_layers = 0;
    for name in super::super::corpus_tests::CORPUS {
        let artifact: cs::gkr_compiler::GKRCircuitArtifact<Bf> =
            serde_json::from_slice(&std::fs::read(dir.join(name)).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        expected_layers += dag.layers.len();
        let fields = crate::analysis::build_cross_layer_field_map(&dag);
        let candidate = compile_r0(&dag).unwrap();
        assert_eq!(dag.layers.len(), candidate.len());
        for (layer, candidate) in candidate.iter().enumerate() {
            let distilled = super::super::common::distill::distill(
                &dag.layers[layer],
                crate::BwdRegime::R0,
                &fields,
            );
            for row in [0, 1, 7] {
                for point in [0, 1, 2, 17] {
                    let x = lift(point);
                    assert_eq!(
                        expression(&distilled.layer, row, x),
                        expanded(&candidate.coefficients, row, x),
                        "{name} L{} row={row} x={point}",
                        layer
                    );
                }
            }
            layers += 1;
        }
    }
    assert!(expected_layers > 0);
    assert_eq!(layers, expected_layers);
}

mod grouping;
mod ordering;

fn load_dag(name: &str) -> gkr_eval_ir::DagCircuit {
    let directory =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let artifact: cs::gkr_compiler::GKRCircuitArtifact<Bf> =
        serde_json::from_slice(&std::fs::read(directory.join(name)).unwrap()).unwrap();
    gkr_eval_ir::lower_dag(&artifact).unwrap()
}
