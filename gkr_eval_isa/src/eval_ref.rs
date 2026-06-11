//! Direct evaluation of an IR arena on one row, lifted to BabyBearExt4.

use cs::gkr_compiler::codegen_ir::{Domain, ExprNode};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};
use rand::{Rng, SeedableRng, rngs::StdRng};

pub type Bf = BabyBearField;
pub type Ext = BabyBearExt4;

pub fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

/// Per-row values for every leaf the arena cannot compute (Place/GateOutput):
/// indexed by arena node id; `None` for computable nodes.
pub struct RowAssignment {
    pub leaf_vals: Vec<Option<Ext>>,
}

/// Random row: bf leaves get random bf (lifted); e4 leaves random e4.
/// Public (not cfg(test)) — the integration oracle uses it.
pub fn random_row(arena: &[ExprNode], rng: &mut StdRng) -> RowAssignment {
    let mut leaf_vals = vec![None; arena.len()];
    for (i, n) in arena.iter().enumerate() {
        let domain = match n {
            ExprNode::Place { domain, .. } | ExprNode::GateOutput { domain, .. } => domain,
            _ => continue,
        };
        let mut rb = |rng: &mut StdRng| Bf::from_u32_with_reduction(rng.random::<u32>());
        leaf_vals[i] = Some(match domain {
            Domain::Base => lift(rb(rng)),
            Domain::Ext => {
                <Ext as FieldExtension<Bf>>::from_coeffs([rb(rng), rb(rng), rb(rng), rb(rng)])
            }
        });
    }
    RowAssignment { leaf_vals }
}

/// Evaluate every node of the arena once. Arena ids are topological
/// (children < parent), so a single forward pass suffices.
pub fn eval_all(arena: &[ExprNode], row: &RowAssignment) -> Vec<Ext> {
    let mut vals: Vec<Ext> = Vec::with_capacity(arena.len());
    for (i, n) in arena.iter().enumerate() {
        let v = match n {
            ExprNode::Constant(c) => lift(Bf::from_u32_with_reduction(*c)),
            ExprNode::Place { .. } | ExprNode::GateOutput { .. } => row.leaf_vals[i]
                .expect("leaf value must be assigned for Place/GateOutput"),
            ExprNode::Sum { terms, .. } => {
                let mut acc = Ext::ZERO;
                for t in terms {
                    acc.add_assign(&vals[t.0 as usize]);
                }
                acc
            }
            ExprNode::Product { factors, .. } => {
                let mut acc = Ext::ONE;
                for f in factors {
                    acc.mul_assign(&vals[f.0 as usize]);
                }
                acc
            }
        };
        vals.push(v);
    }
    vals
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use gkr_design_space::import::load_circuit;

    pub(crate) fn fixture(name: &str) -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../cs/compiled_circuits")
            .join(name)
    }

    #[test]
    fn evaluates_add_sub_layer0() {
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let arena = &c.circuit.layers[0].arena.nodes;
        let mut rng = StdRng::seed_from_u64(42);
        let row = random_row(arena, &mut rng);
        let vals = eval_all(arena, &row);
        assert_eq!(vals.len(), 224); // verified add_sub L0 node count
        // Determinism: same seed, same values.
        let row2 = random_row(arena, &mut StdRng::seed_from_u64(42));
        assert_eq!(eval_all(arena, &row2), vals);
    }
}
