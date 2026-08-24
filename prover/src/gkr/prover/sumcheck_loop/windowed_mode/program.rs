//! Shared batched-program representation for the same-size LSB sumcheck
//! engines: CSE'd bracket forms + factored products compiled DIRECTLY from
//! the layer's [`NoFieldStructuredExpression`] trees (for the max-quadratic
//! relation kinds), plus the expanded remainder of every other kernel from
//! the flattened batched description. Consumed by the uniskip/window chain
//! kernels (`lsb_bench`, `lsb_generic`) and the chain driver (`lsb_chain`).
//!
//! # Cell semantics of form constants
//!
//! A form may be MIXED-degree (an affine `c + sum a_i * slot_i`): its
//! constant part contributes to evaluations (the binary cells / real domain
//! points) but NEVER to difference/infinity cells — a constant has no
//! leading coefficient. Every kernel that materializes a form grid must add
//! [`FormDesc::constant`] only at those cells.

use std::collections::{BTreeMap, BTreeSet};

use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;
use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelCollector;
use crate::gkr::sumcheck::evaluation_kernels::generic_kernel::BatchedGKRTermDescriptionConstants;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation, NoFieldStructuredExpression};
use field::{Field, FieldExtension, PrimeField};

/// One inner-linear-form member of a preserved bracket.
#[derive(Clone, Copy)]
pub enum FormOp<F: PrimeField> {
    Add,
    Sub,
    Mul(F),
}

/// One CSE'd bracket form: an affine combination of BASE slots plus a
/// constant (see the module docs for the constant's cell semantics).
#[derive(Clone)]
pub struct FormDesc<F: PrimeField> {
    pub members: Vec<(FormOp<F>, u16)>,
    pub constant: F,
}

/// One operand of a factored quadratic product: a raw base slot's grid, or
/// a materialized form's grid.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FormRef {
    Slot(u16),
    Form(u16),
}

/// Expanded (monomial) step over the full scratch layout, used by the
/// bracket-preserving evaluator for everything that is not a preserved bracket.
#[derive(Clone, Copy)]
pub enum ProgramStep<E: Field> {
    QuadBB { a: u16, b: u16, c: E },
    QuadBE { base: u16, ext: u16, c: E },
    QuadEE { a: u16, b: u16, c: E },
    LinB { i: u16, c: E },
    LinE { i: u16, c: E },
}

/// Slot-schedule step for the tiled uniskip evaluator. Base-pool indices
/// < `num_base` are real polys; >= `num_base` are bracket forms (materialized
/// from source taps on load, so forms do not pin their member grids).
#[derive(Clone)]
pub enum TiledStep<E: Field> {
    LoadBase {
        slot: u16,
        idx: u16,
    },
    LoadExt {
        slot: u16,
        idx: u16,
    },
    /// combine the form's members from their RESIDENT grids (all 128 cells --
    /// LDE is linear, so the coset half combines directly) into `slot`
    BuildForm {
        slot: u16,
        form: u16,
        member_slots: Vec<u16>,
    },
    QuadBB {
        sa: u16,
        sb: u16,
        c: E,
    },
    QuadBE {
        sb: u16,
        se: u16,
        c: E,
    },
    QuadEE {
        sa: u16,
        sb: u16,
        c: E,
    },
    LinB {
        slot: u16,
        c: E,
    },
    LinE {
        slot: u16,
        c: E,
    },
}

/// Owned SoA + bracket program for one layer, consumed by the production
/// windowed sumcheck loop (mirrors the program the bench driver builds inline).
pub struct OwnedSoaProgram<F: PrimeField, E: Field> {
    pub base_interp: Vec<bool>,
    pub ext_interp: Vec<bool>,
    pub forms: Vec<FormDesc<F>>,
    /// Factored quadratic products `c * A(x) * B(x)` over slot/form grids.
    pub products: Vec<(FormRef, FormRef, E)>,
    pub rest_steps: Vec<ProgramStep<E>>,
    pub folded_quad: Vec<(u16, u16, E)>,
    pub folded_lin: Vec<(u16, E)>,
    pub additive_constant: E,
}

/// A degree-<=1 polynomial in the layer inputs: `constant + sum c_i * addr_i`.
#[derive(Clone)]
struct Affine<F: PrimeField> {
    constant: F,
    linear: BTreeMap<GKRAddress, F>,
}

impl<F: PrimeField> Affine<F> {
    fn zero() -> Self {
        Self {
            constant: F::ZERO,
            linear: BTreeMap::new(),
        }
    }
    fn scale(&mut self, c: &F) {
        self.constant.mul_assign(c);
        for v in self.linear.values_mut() {
            v.mul_assign(c);
        }
    }
    fn add(&mut self, other: &Self) {
        self.constant.add_assign(&other.constant);
        for (a, c) in other.linear.iter() {
            self.linear.entry(*a).or_insert(F::ZERO).add_assign(c);
        }
    }
}

/// A degree-<=2 polynomial with the quadratic part kept FACTORED as
/// `scale * A(x) * B(x)` pairs of affine forms -- the shape the windowed
/// cell evaluators consume without expansion.
#[derive(Clone)]
struct QPoly<F: PrimeField> {
    affine: Affine<F>,
    quads: Vec<(F, Affine<F>, Affine<F>)>,
}

/// Compiles a [`NoFieldStructuredExpression`] tree into the factored
/// normal form. Returns `None` for shapes beyond max-quadratic (the caller
/// falls back to the flattened path for that relation).
fn compile_expression<F: PrimeField>(e: &NoFieldStructuredExpression<F>) -> Option<QPoly<F>> {
    match e {
        NoFieldStructuredExpression::Constant(c) => Some(QPoly {
            affine: Affine {
                constant: *c,
                linear: BTreeMap::new(),
            },
            quads: vec![],
        }),
        NoFieldStructuredExpression::Place(a) => {
            let mut linear = BTreeMap::new();
            linear.insert(*a, F::ONE);
            Some(QPoly {
                affine: Affine {
                    constant: F::ZERO,
                    linear,
                },
                quads: vec![],
            })
        }
        NoFieldStructuredExpression::Sum(children) => {
            let mut acc = QPoly {
                affine: Affine::zero(),
                quads: vec![],
            };
            for ch in children.iter() {
                let part = compile_expression(ch)?;
                acc.affine.add(&part.affine);
                acc.quads.extend(part.quads);
            }
            Some(acc)
        }
        NoFieldStructuredExpression::Product(children) => {
            let mut scale = F::ONE;
            let mut affines: Vec<Affine<F>> = vec![];
            let mut quad: Option<QPoly<F>> = None;
            for ch in children.iter() {
                let part = compile_expression(ch)?;
                if part.quads.is_empty() && part.affine.linear.is_empty() {
                    // pure constant factor
                    scale.mul_assign(&part.affine.constant);
                } else if part.quads.is_empty() {
                    affines.push(part.affine);
                } else {
                    // a factor that already carries quadratic terms may only
                    // be multiplied by constants
                    if quad.is_some() {
                        return None;
                    }
                    quad = Some(part);
                }
            }
            match (quad, affines.len()) {
                (None, 0) => Some(QPoly {
                    affine: Affine {
                        constant: scale,
                        linear: BTreeMap::new(),
                    },
                    quads: vec![],
                }),
                (None, 1) => {
                    let mut a = affines.pop().expect("one affine");
                    a.scale(&scale);
                    Some(QPoly {
                        affine: a,
                        quads: vec![],
                    })
                }
                (None, 2) => {
                    let b = affines.pop().expect("two affines");
                    let a = affines.pop().expect("two affines");
                    Some(QPoly {
                        affine: Affine::zero(),
                        quads: vec![(scale, a, b)],
                    })
                }
                (Some(mut q), 0) => {
                    q.affine.scale(&scale);
                    for (s, _, _) in q.quads.iter_mut() {
                        s.mul_assign(&scale);
                    }
                    Some(q)
                }
                // quad * affine or > 2 affine factors: beyond max-quadratic
                _ => None,
            }
        }
    }
}

/// Build the SoA + bracket-preserving program for a layer.
///
/// Max-quadratic relations (`NoFieldGKRRelation::MaxQuadratic` /
/// `::EnforceSingleMaxQuadraticConstraint`) compile DIRECTLY from their
/// [`NoFieldStructuredExpression`] trees: quadratic terms stay factored as
/// (possibly mixed-degree) form-by-form products, so nothing is expanded and
/// re-recovered. Every other kernel -- and any structured relation whose
/// expression the compiler cannot lower (non-base places, exotic shapes) --
/// goes through the flattened batched description as before, built here with
/// the expression-compiled kernels EXCLUDED so no term is double-counted.
///
/// The FULL `description` is used only for the interpolation flags (quad
/// participation there is a superset of the factored products').
pub fn build_soa_program<F: PrimeField, E: FieldExtension<F> + Field>(
    description: &BatchedGKRDescription<F, E>,
    collector: &KernelCollector<F, E>,
    layer_desc: &GKRLayerDescription<F>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    base_polys: &[GKRAddress],
    ext_polys: &[GKRAddress],
) -> OwnedSoaProgram<F, E> {
    use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelVariant;

    // slot lookup by map instead of a linear scan per term (the slot lists
    // are BTreeSet-ordered, so enumeration == slot index)
    let base_map: BTreeMap<GKRAddress, u16> = base_polys
        .iter()
        .enumerate()
        .map(|(i, a)| (*a, i as u16))
        .collect();
    let ext_map: BTreeMap<GKRAddress, u16> = ext_polys
        .iter()
        .enumerate()
        .map(|(i, a)| (*a, i as u16))
        .collect();
    let bidx = |addr: &GKRAddress| base_map[addr];
    let eidx = |addr: &GKRAddress| ext_map[addr];

    let mut base_quad: BTreeSet<GKRAddress> = BTreeSet::new();
    let mut ext_quad: BTreeSet<GKRAddress> = BTreeSet::new();
    for (a, list) in description.quadratic_part_base_by_base.iter() {
        base_quad.insert(*a);
        for (b, _) in list.iter() {
            base_quad.insert(*b);
        }
    }
    for (a, list) in description.quadratic_part_base_by_ext.iter() {
        base_quad.insert(*a);
        for (b, _) in list.iter() {
            ext_quad.insert(*b);
        }
    }
    for (a, list) in description.quadratic_part_ext_by_ext.iter() {
        ext_quad.insert(*a);
        for (b, _) in list.iter() {
            ext_quad.insert(*b);
        }
    }
    let mut base_interp: Vec<bool> = base_polys.iter().map(|a| base_quad.contains(a)).collect();
    let ext_interp: Vec<bool> = ext_polys.iter().map(|a| ext_quad.contains(a)).collect();

    let mut forms: Vec<FormDesc<F>> = vec![];
    let mut form_key_to_idx: BTreeMap<(u128, Vec<(u16, u128)>), u16> = BTreeMap::new();
    let mut products: Vec<(FormRef, FormRef, E)> = vec![];
    let mut rest_steps: Vec<ProgramStep<E>> = vec![];
    let mut additive_constant = E::ZERO;

    // lower one affine quad factor to a grid operand: a bare unit-coefficient
    // slot stays a slot reference; everything else becomes a CSE'd form
    let mut operand = |a: &Affine<F>| -> FormRef {
        if a.constant.is_zero() && a.linear.len() == 1 {
            let (addr, c) = a.linear.iter().next().expect("one member");
            if *c == F::ONE {
                return FormRef::Slot(bidx(addr));
            }
        }
        let key: (u128, Vec<(u16, u128)>) = (
            a.constant.as_u128_reduced(),
            a.linear
                .iter()
                .map(|(addr, c)| (bidx(addr), c.as_u128_reduced()))
                .collect(),
        );
        let next_idx = forms.len() as u16;
        FormRef::Form(*form_key_to_idx.entry(key).or_insert_with(|| {
            let members: Vec<(FormOp<F>, u16)> = a
                .linear
                .iter()
                .map(|(addr, c)| {
                    let op = if *c == F::ONE {
                        FormOp::Add
                    } else if *c == F::MINUS_ONE {
                        FormOp::Sub
                    } else {
                        FormOp::Mul(*c)
                    };
                    (op, bidx(addr))
                })
                .collect();
            forms.push(FormDesc {
                members,
                constant: a.constant,
            });
            next_idx
        }))
    };

    // -- expression-compiled relations: walk the layer gates in the same
    // order the collector built its kernels (one kernel per gate)
    let mut expression_kernels: BTreeSet<usize> = BTreeSet::new();
    let gates_iter = layer_desc
        .gates
        .iter()
        .chain(layer_desc.gates_with_external_connections.iter());
    for (ki, (gate, kernel)) in gates_iter.zip(collector.kernels.iter()).enumerate() {
        let expression = match &gate.enforced_relation {
            NoFieldGKRRelation::MaxQuadratic { expression, .. }
            | NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { expression, .. } => {
                expression
            }
            _ => continue,
        };
        let challenge = match kernel {
            KernelVariant::MaxQuadratic(_, ch, _) => ch[0],
            KernelVariant::EnforceSingleMaxQuadraticConstraint(_, ch) => ch[0],
            other => panic!(
                "gate/kernel order diverged: structured gate paired with {:?}",
                other
            ),
        };
        let Some(q) = compile_expression(expression) else {
            // beyond max-quadratic shape: leave this kernel on the flattened path
            continue;
        };
        // max-quadratic gate expressions are BASE-ONLY by construction:
        // every place they reference is a base-field slot. Keeping that as
        // the compiled-program invariant (checked here, flattened fallback
        // if it ever breaks) lets the SIMD kernels run every compiled
        // product through the base*base lazy path and every compiled linear
        // term as LinB -- no ext dispatch anywhere in the expression part.
        let base_only = q
            .quads
            .iter()
            .flat_map(|(_, a, b)| a.linear.keys().chain(b.linear.keys()))
            .chain(q.affine.linear.keys())
            .all(|k| base_map.contains_key(k));
        if !base_only {
            continue;
        }
        expression_kernels.insert(ki);

        let mut c = challenge;
        c.mul_assign_by_base(&q.affine.constant);
        additive_constant.add_assign(&c);
        for (addr, coeff) in q.affine.linear.iter() {
            let mut c = challenge;
            c.mul_assign_by_base(coeff);
            rest_steps.push(ProgramStep::LinB { i: bidx(addr), c });
        }
        for (scale, a, b) in q.quads.iter() {
            let ra = operand(a);
            let rb = operand(b);
            let mut c = challenge;
            c.mul_assign_by_base(scale);
            products.push((ra, rb, c));
        }
    }

    // -- everything else: the flattened description over the REMAINING kernels
    let rest = collector.make_batched_description_excluding(
        challenge_constants,
        collector.layer,
        &expression_kernels,
    );
    for (a, list) in rest.quadratic_part_base_by_base.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(ProgramStep::QuadBB {
                a: bidx(a),
                b: bidx(b),
                c: *c,
            });
        }
    }
    for (a, list) in rest.quadratic_part_base_by_ext.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(ProgramStep::QuadBE {
                base: bidx(a),
                ext: eidx(b),
                c: *c,
            });
        }
    }
    for (a, list) in rest.quadratic_part_ext_by_ext.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(ProgramStep::QuadEE {
                a: eidx(a),
                b: eidx(b),
                c: *c,
            });
        }
    }
    for (a, c) in rest.linear_part_base_by_everything.iter() {
        rest_steps.push(ProgramStep::LinB { i: bidx(a), c: *c });
    }
    for (a, c) in rest.linear_part_ext_by_everything.iter() {
        rest_steps.push(ProgramStep::LinE { i: eidx(a), c: *c });
    }
    additive_constant.add_assign(&rest.constant_term);

    // folded stages over the combined slot space, derived from rest_steps so
    // the expression-compiled linear terms are included automatically
    let nb = base_polys.len() as u16;
    let mut folded_quad: Vec<(u16, u16, E)> = vec![];
    let mut folded_lin: Vec<(u16, E)> = vec![];
    for step in rest_steps.iter() {
        match step {
            ProgramStep::QuadBB { a, b, c } => folded_quad.push((*a, *b, *c)),
            ProgramStep::QuadBE { base, ext, c } => folded_quad.push((*base, nb + *ext, *c)),
            ProgramStep::QuadEE { a, b, c } => folded_quad.push((nb + *a, nb + *b, *c)),
            ProgramStep::LinB { i, c } => folded_lin.push((*i, *c)),
            ProgramStep::LinE { i, c } => folded_lin.push((nb + *i, *c)),
        }
    }

    // The flattened description's quad participation is a superset of the
    // factored program's difference-cell needs only up to CS-side
    // simplification: a factored form may read a slot whose expanded cross
    // terms cancelled out of the flattened relation (keccak_special5 layer 0
    // hits this), so the flags derived above can miss it. The program itself
    // is the authority on which slots it reads at the difference cells.
    for form in forms.iter() {
        for (_, idx) in form.members.iter() {
            base_interp[*idx as usize] = true;
        }
    }
    for (a, b, _) in products.iter() {
        for r in [a, b] {
            if let FormRef::Slot(i) = r {
                base_interp[*i as usize] = true;
            }
        }
    }

    OwnedSoaProgram {
        base_interp,
        ext_interp,
        forms,
        products,
        rest_steps,
        folded_quad,
        folded_lin,
        additive_constant,
    }
}
