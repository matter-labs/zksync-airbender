//! Shared batched-program representation for the same-size LSB sumcheck
//! engines: the CSE'd bracket forms + preserved products + expanded
//! remainder built from a layer's batched description, consumed by the
//! uniskip/window chain kernels (`lsb_bench`, `lsb_generic`) and the chain
//! driver (`lsb_chain`).

use std::collections::BTreeMap;

use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;
use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelCollector;
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};

/// One inner-linear-form member of a preserved bracket.
#[derive(Clone, Copy)]
pub enum FormOp<F: PrimeField> {
    Add,
    Sub,
    Mul(F),
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
pub(crate) struct OwnedSoaProgram<F: PrimeField, E: Field> {
    pub base_interp: Vec<bool>,
    pub ext_interp: Vec<bool>,
    pub forms: Vec<Vec<(FormOp<F>, u16)>>,
    pub products: Vec<(u16, u16, E)>,
    pub rest_steps: Vec<ProgramStep<E>>,
    pub folded_quad: Vec<(u16, u16, E)>,
    pub folded_lin: Vec<(u16, E)>,
    pub additive_constant: E,
}

/// Build the SoA + bracket-preserving program for a layer: interpolation flags,
/// CSE'd multi-member bracket forms + preserved products (from the enforce
/// max-quadratic kernels), the bracket-subtracted expanded remainder, and the
/// folded-stage step lists over the combined slot space.
pub(crate) fn build_soa_program<F: PrimeField, E: FieldExtension<F> + Field>(
    description: &BatchedGKRDescription<F, E>,
    collector: &KernelCollector<F, E>,
    base_polys: &[GKRAddress],
    ext_polys: &[GKRAddress],
) -> OwnedSoaProgram<F, E> {
    use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelVariant;
    use std::collections::BTreeSet;

    let bidx = |addr: &GKRAddress| base_polys.iter().position(|el| el == addr).unwrap() as u16;
    let eidx = |addr: &GKRAddress| ext_polys.iter().position(|el| el == addr).unwrap() as u16;

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
    let base_interp: Vec<bool> = base_polys.iter().map(|a| base_quad.contains(a)).collect();
    let ext_interp: Vec<bool> = ext_polys.iter().map(|a| ext_quad.contains(a)).collect();

    let mut forms: Vec<Vec<(FormOp<F>, u16)>> = vec![];
    let mut form_key_to_idx: BTreeMap<Vec<(u128, u16)>, u16> = BTreeMap::new();
    let mut products: Vec<(u16, u16, E)> = vec![];
    let mut subtract: BTreeMap<(GKRAddress, GKRAddress), E> = BTreeMap::new();

    for kernel in collector.kernels.iter() {
        let KernelVariant::EnforceSingleMaxQuadraticConstraint(rel, ch) = kernel else {
            continue;
        };
        let challenge = ch[0];
        for (a, bracket) in rel.relation.quadratic_terms.iter() {
            let members: Vec<(F, GKRAddress)> = bracket
                .iter()
                .filter(|(c, _)| !c.is_zero())
                .copied()
                .collect();
            if members.len() < 2 {
                continue;
            }
            for (c, b) in members.iter() {
                let pair = if *a <= *b { (*a, *b) } else { (*b, *a) };
                let mut contribution = challenge;
                contribution.mul_assign_by_base(c);
                subtract
                    .entry(pair)
                    .or_insert(E::ZERO)
                    .add_assign(&contribution);
            }
            let mut key: Vec<(u128, u16)> = members
                .iter()
                .map(|(c, b)| (c.as_u128_reduced(), bidx(b)))
                .collect();
            key.sort();
            let form_idx = *form_key_to_idx.entry(key).or_insert_with(|| {
                let ops: Vec<(FormOp<F>, u16)> = members
                    .iter()
                    .map(|(c, b)| {
                        let op = if *c == F::ONE {
                            FormOp::Add
                        } else if *c == F::MINUS_ONE {
                            FormOp::Sub
                        } else {
                            FormOp::Mul(*c)
                        };
                        (op, bidx(b))
                    })
                    .collect();
                forms.push(ops);
                (forms.len() - 1) as u16
            });
            products.push((bidx(a), form_idx, challenge));
        }
    }

    let mut rest_steps: Vec<ProgramStep<E>> = vec![];
    for (a, list) in description.quadratic_part_base_by_base.iter() {
        for (b, c) in list.iter() {
            let mut c = *c;
            if let Some(sub) = subtract.get(&(*a, *b)) {
                c.sub_assign(sub);
            }
            if c.is_zero() {
                continue;
            }
            rest_steps.push(ProgramStep::QuadBB {
                a: bidx(a),
                b: bidx(b),
                c,
            });
        }
    }
    for (a, list) in description.quadratic_part_base_by_ext.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(ProgramStep::QuadBE {
                base: bidx(a),
                ext: eidx(b),
                c: *c,
            });
        }
    }
    for (a, list) in description.quadratic_part_ext_by_ext.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(ProgramStep::QuadEE {
                a: eidx(a),
                b: eidx(b),
                c: *c,
            });
        }
    }
    for (a, c) in description.linear_part_base_by_everything.iter() {
        rest_steps.push(ProgramStep::LinB { i: bidx(a), c: *c });
    }
    for (a, c) in description.linear_part_ext_by_everything.iter() {
        rest_steps.push(ProgramStep::LinE { i: eidx(a), c: *c });
    }

    let nb = base_polys.len() as u16;
    let mut folded_quad: Vec<(u16, u16, E)> = vec![];
    for step in rest_steps.iter() {
        match step {
            ProgramStep::QuadBB { a, b, c } => folded_quad.push((*a, *b, *c)),
            ProgramStep::QuadBE { base, ext, c } => folded_quad.push((*base, nb + *ext, *c)),
            ProgramStep::QuadEE { a, b, c } => folded_quad.push((nb + *a, nb + *b, *c)),
            _ => {}
        }
    }
    let mut folded_lin: Vec<(u16, E)> = vec![];
    for (a, c) in description.linear_part_base_by_everything.iter() {
        folded_lin.push((bidx(a), *c));
    }
    for (a, c) in description.linear_part_ext_by_everything.iter() {
        folded_lin.push((nb + eidx(a), *c));
    }

    OwnedSoaProgram {
        base_interp,
        ext_interp,
        forms,
        products,
        rest_steps,
        folded_quad,
        folded_lin,
        additive_constant: description.constant_term,
    }
}
