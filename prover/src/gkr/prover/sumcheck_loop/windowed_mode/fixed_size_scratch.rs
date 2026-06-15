use std::collections::BTreeSet;

use super::*;
use crate::gkr::prover::sumcheck::access_and_fold::*;
use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluationStep {
    LoadBaseIntoScratch {
        scratch_idx: u8,
        interpolate_at_inf: bool,
        src_idx: u32,
    },
    LoadExtIntoScratch {
        scratch_idx: u8,
        interpolate_at_inf: bool,
        src_idx: u32,
    },
    QuadraticBaseByBase(usize), // index of the coefficient
    QuadraticBaseByExt {
        scratch_idx_base: u8,
        scratch_idx_ext: u8,
        coeff_idx: u32,
    },
    QuadraticExtByExt(usize),
    LinearWithBase{
        scratch_idx: u8,
        coeff_idx: u32,
    },
    LinearWithExt{
        scratch_idx: u8,
        coeff_idx: u32,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldedEvaluationStep {
    LoadIntoScratch{
        scratch_idx: u8,
        interpolate_at_inf: bool,
        src_idx: u32,
    },
    Quadratic(usize), // index of the coefficient
    Linear(usize),
}

pub struct BatchEvaluationFSMDescription<F: PrimeField, E: FieldExtension<F> + Field>{
    initial_evaluation_steps: Vec<EvaluationStep>,
    folded_evaluation_steps: Vec<FoldedEvaluationStep>,
    constants: Vec<E>,
    total_additive_constant: E,
    _marker: core::marker::PhantomData<F>,
}

#[inline(always)]
fn interpolate_at_inf_from_0_1_basis<F: Field>(a: F, b: F) -> F {
    let mut result = b;
    result.sub_assign(&a);
    result
}

#[inline(always)]
fn read_and_interpolate_field<F: Field>(
    dst: &mut [F; 27],
    src: &DisjointAccessQuasiSlice<F, false>,
    input_size: usize,
    row: usize,
) {
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                dst[dst_offset] = src.read(src_0_idx);
                dst[dst_offset + 1] = src.read(src_1_idx);
                dst[dst_offset + 2] =
                    interpolate_at_inf_from_0_1_basis(dst[dst_offset], dst[dst_offset + 1]);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }

        // now get inf over x1
        for x2 in 0..3 {
            let src_0_idx = dst_offset + x2;
            let src_1_idx = dst_offset + 3 + x2;
            dst[dst_offset + 3 * 2 + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }

    // and get inf over x0
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_0_idx = 0 + dst_offset + x2;
            let src_1_idx = 9 + dst_offset + x2;
            dst[18 + dst_offset + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }
}

#[inline(always)]
fn read_without_interpolation<F: Field>(
    dst: &mut [F; 27],
    src: &DisjointAccessQuasiSlice<F, false>,
    input_size: usize,
    row: usize,
) {
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                dst[dst_offset] = src.read(src_0_idx);
                dst[dst_offset + 1] = src.read(src_1_idx);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }
    }
}

#[inline(always)]
fn evaluate_quadratic_base<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    a: &[F; 27],
    b: &[F; 27],
    prefactor: &E
) {
    for i in 0..27 {
        let mut t = a[i];
        t.mul_assign(&b[i]);
        let mut acc = *prefactor;
        acc.mul_assign_by_base(&t);
        dst[i].add_assign(&acc);
    }
}

#[inline(always)]
fn evaluate_quadratic_mixed<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    a: &[E; 27],
    b: &[F; 27],
    prefactor: &E
) {
    for i in 0..27 {
        let mut t = a[i];
        t.mul_assign_by_base(&b[i]);
        let mut acc = *prefactor;
        acc.mul_assign(&t);
        dst[i].add_assign(&acc);
    }
}

#[inline(always)]
fn evaluate_quadratic_ext<F: Field>(
    dst: &mut [F; 27],
    a: &[F; 27],
    b: &[F; 27],
    prefactor: &F
) {
    for i in 0..27 {
        let mut t = a[i];
        t.mul_assign(&b[i]);
        let mut acc = *prefactor;
        acc.mul_assign(&t);
        dst[i].add_assign(&acc);
    }
}

#[inline(always)]
fn evaluate_linear_base<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    a: &[F; 27],
    prefactor: &E
) {
    // we only need a limited set of terms
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for k in 0..2 {
                let mut acc = *prefactor;
                let t = a[offset + k];
                acc.mul_assign_by_base(&t);
                dst[offset + k].add_assign(&acc);
            }
        }
    }
}

#[inline(always)]
fn evaluate_linear_ext<F: Field>(
    dst: &mut [F; 27],
    a: &[F; 27],
    prefactor: &F
) {
    // we only need a limited set of terms
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for k in 0..2 {
                let mut acc = *prefactor;
                let t = a[offset + k];
                acc.mul_assign(&t);
                dst[offset + k].add_assign(&acc);
            }
        }
    }
}

pub fn evaluate_initial<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    description: &BatchEvaluationFSMDescription<F, E>,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    row_range: core::ops::Range<usize>,
) -> [E; 27] {
    // NOTE: assuming typical L1 cache size of 32Kb we can fit up to 2k ext field elements for 4th extension, or ~75 ext field fully read
    // and interpolated sets. That is more than sufficient for all our circuits except precompiles, and so we can actually use a strategy to read once
    // and then compute
    assert!(input_size_log2 >= 4);
    assert_eq!(precomputed_eq_suffix.len(), 1 << (input_size_log2 - 3));
    let mut accumulator = [E::ZERO; 27];

    let input_size = 1 << input_size_log2;

    let mut base_field_scratch = [[F::ZERO; 27]; 2];
    let mut ext_field_scratch = [[E::ZERO; 27]; 2];
    let mut eval_scratch = [E::ZERO; 27];

    for row in row_range {
        let eq_prefactor = &precomputed_eq_suffix[row];
        eval_scratch.fill(E::ZERO);

        for step in description.initial_evaluation_steps.iter() {
            match *step {
                EvaluationStep::LoadBaseIntoScratch { scratch_idx, interpolate_at_inf, src_idx } => {
                    let dst = &mut base_field_scratch[scratch_idx as usize];
                    let src = &base_field_inputs[src_idx as usize];
                    if interpolate_at_inf {
                        read_and_interpolate_field(
                            dst,
                            src,
                            input_size,
                            row,
                        );
                    } else {
                        read_without_interpolation(dst, src, input_size, row);
                    }
                },
                EvaluationStep::LoadExtIntoScratch { scratch_idx, interpolate_at_inf, src_idx } => {
                    let dst = &mut ext_field_scratch[scratch_idx as usize];
                    let src = &ext_field_inputs[src_idx as usize];
                    if interpolate_at_inf {
                        read_and_interpolate_field(
                            dst,
                            src,
                            input_size,
                            row,
                        );
                    } else {
                        read_without_interpolation(dst, src, input_size, row);
                    }
                },
                EvaluationStep::QuadraticBaseByBase(coeff_idx) => {
                    let coeff = description.constants[coeff_idx];
                    evaluate_quadratic_base(
                        &mut eval_scratch,
                        &base_field_scratch[0],
                        &base_field_scratch[1],
                        &coeff,
                    );
                }
                EvaluationStep::QuadraticBaseByExt{
                        scratch_idx_base,
                        scratch_idx_ext,
                        coeff_idx,
                    } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_quadratic_mixed(
                        &mut eval_scratch,
                        &ext_field_scratch[scratch_idx_ext as usize],
                        &base_field_scratch[scratch_idx_base as usize],
                        &coeff,
                    );
                }
                EvaluationStep::QuadraticExtByExt(coeff_idx) => {
                    let coeff = description.constants[coeff_idx];
                    evaluate_quadratic_ext(
                        &mut eval_scratch,
                        &ext_field_scratch[0],
                        &ext_field_scratch[1],
                        &coeff,
                    );
                }
                EvaluationStep::LinearWithBase { scratch_idx, coeff_idx } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_linear_base(
                        &mut eval_scratch,
                        &base_field_scratch[scratch_idx as usize],
                        &coeff,
                    );
                }
                EvaluationStep::LinearWithExt { scratch_idx, coeff_idx } => {
                    let coeff = description.constants[coeff_idx as usize];
                    evaluate_linear_ext(
                        &mut eval_scratch,
                        &ext_field_scratch[scratch_idx as usize],
                        &coeff,
                    );
                }
            }
        }

        if description.total_additive_constant.is_zero() == false {
            // only terms that are not at infinity
            for i in 0..2 {
                let offset = 9 * i;
                for j in 0..2 {
                    let offset = offset + 3 * j;
                    for k in 0..2 {
                        eval_scratch[offset + k].add_assign(&description.total_additive_constant);
                    }
                }
            }
        }

        for i in 0..27 {
            let mut t = eval_scratch[i];
            t.mul_assign(eq_prefactor);
            accumulator[i].add_assign(&t);
        }
    }

    accumulator
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchEvaluationFSMDescription<F, E> {
    pub fn from_batched_description(description: &BatchedGKRDescription<F, E>) -> (Self, Vec<GKRAddress>, Vec<GKRAddress>) {
        let mut all_base_sources = BTreeSet::new();
        let mut all_ext_sources = BTreeSet::new();
        
        for (a, other) in description.quadratic_part_base_by_base.iter() {
            all_base_sources.insert(*a);
            for (b, _) in other.iter() {
                all_base_sources.insert(*b);
            }
        }

        for (a, other) in description.quadratic_part_base_by_ext.iter() {
            all_base_sources.insert(*a);
            for (b, _) in other.iter() {
                all_ext_sources.insert(*b);
            }
        }

        for (a, other) in description.quadratic_part_base_by_ext.iter() {
            all_ext_sources.insert(*a);
            for (b, _) in other.iter() {
                all_ext_sources.insert(*b);
            }
        }

        for (a, _) in description.linear_part_base_by_everything.iter() {
            all_base_sources.insert(*a);
        }
        for (a, _) in description.linear_part_ext_by_everything.iter() {
            all_ext_sources.insert(*a);
        }

        let base_sources: Vec<_> = all_base_sources.iter().copied().collect();
        let ext_sources: Vec<_> = all_ext_sources.iter().copied().collect();

        let mut base_mapping = BTreeMap::new();
        for src in all_base_sources.iter() {
            let idx = base_sources.iter().position(|el| *el == *src).expect("position");
            base_mapping.insert(*src, idx);
        }
        let mut ext_mapping = BTreeMap::new();
        for src in all_ext_sources.iter() {
            let idx = ext_sources.iter().position(|el| *el == *src).expect("position");
            ext_mapping.insert(*src, idx);
        }

        // now we can try to use different optimization strategies how to transform a flat relation into evaluation FSM, but
        // we will try to do a naive one with merging linear and quadratic via single read, and first evaluating longest chains for products

        let mut all_coefficients = vec![];


        (todo!(), base_sources, ext_sources)
    }
}