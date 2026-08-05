//! BENCH-ONLY experiment: fused `transition in3out1` + `ext in1out3` pass.
//!
//! The separate chain writes every poly's fold-by-(w0..w2) values (2^21 ext
//! elements per poly) and the next pass reads them straight back to fold w3.
//! This fused sweep computes the 16 fold values a `in1out3` row needs directly
//! from the ORIGINAL polys, evaluates BOTH the round-3 `[E; 2]` accumulator and
//! the rounds-4..6 27-cell accumulator, and writes only the final
//! fold-by-(w0..w3) buffer (2^20 per poly) — eliminating the intermediate
//! write+read entirely.
//!
//! CAVEAT: this consumes `w3` while round 3's univariate is still being
//! accumulated, which inverts the transcript order — invalid in the real
//! protocol. It exists to measure the ceiling of the read+write merge; a
//! protocol-valid version would use an `in 3, out 4` window (81 cells) instead.

use super::*;
use crate::gkr::PAR_THRESHOLD;

pub(crate) fn evaluate_merged_transition_in1out3_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    base_field_inputs: Vec<DisjointAccessQuasiSlice<F, false>>,
    ext_field_inputs: Vec<DisjointAccessQuasiSlice<E, false>>,
    base_field_folding_buffers: Vec<DisjointAccessQuasiSlice<E, true>>,
    ext_field_folding_buffers: Vec<DisjointAccessQuasiSlice<E, true>>,
    description: &BatchEvaluationCompactDescription<F, E>,
    precomputed_eq_prefix: &[E; 8],
    w3: &E,
    eq_mid: &[E],    // len 8, over prev[4..7]
    eq_suffix: &[E], // len 2^(n-7), over prev[7..]
    input_size_log2: usize,
    worker: &Worker,
) -> ([E; 2], [E; 27]) {
    assert_eq!(
        description.base_read_with_interpolation.len(),
        base_field_inputs.len()
    );
    assert_eq!(
        description.ext_read_with_interpolation.len(),
        ext_field_inputs.len()
    );
    let num_base = base_field_inputs.len();
    let num_polys = num_base + ext_field_inputs.len();

    let input_size = 1 << input_size_log2;
    let fold_stride = input_size / 8; // 2^21: tap distance of the 8-tap fold
    let half = fold_stride / 2; // 2^20: the w3 pair distance
    let corner_strides = [half / 2, half / 4, half / 8]; // window vars of rounds 4-6
    let work_size = half / 8; // 2^17 rows
    assert_eq!(eq_mid.len(), 8);
    assert_eq!(eq_suffix.len(), work_size);

    let geometry = worker.get_geometry_with_threshold(work_size, PAR_THRESHOLD);
    let mut results = vec![([E::ZERO; 2], [E::ZERO; 27]); geometry.num_chunks];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = results.iter_mut();
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let range = chunk_start..(chunk_start + chunk_size);
            let dst = it.next().unwrap();
            let base_field_inputs = base_field_inputs.clone();
            let ext_field_inputs = ext_field_inputs.clone();
            let mut base_buffers = base_field_folding_buffers.clone();
            let mut ext_buffers = ext_field_folding_buffers.clone();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut pairs: Vec<[[E; 2]; 8]> = vec![[[E::ZERO; 2]; 8]; num_polys];
                let mut grids: Vec<[E; 27]> = vec![[E::ZERO; 27]; num_polys];
                let mut acc2 = [E::ZERO; 2];
                let mut acc27 = [E::ZERO; 27];
                let mut eval2 = [E::ZERO; 2];
                let mut eval27 = [E::ZERO; 27];

                for row in range {
                    // fold all polys: 16 direct 8-tap folds per poly, fold w3 in
                    // registers, write only the final folded value
                    for (poly_idx, src) in base_field_inputs.iter().enumerate() {
                        let scratch_pairs = &mut pairs[poly_idx];
                        let grid = &mut grids[poly_idx];
                        for j in 0..8usize {
                            let pos = row
                                + (j >> 2) * corner_strides[0]
                                + ((j >> 1) & 1) * corner_strides[1]
                                + (j & 1) * corner_strides[2];
                            let (v0, v1) = read_base_and_fold_pair(
                                src,
                                precomputed_eq_prefix,
                                fold_stride,
                                pos,
                                pos + half,
                            );
                            let mut d = v1;
                            d.sub_assign(&v0);
                            scratch_pairs[j] = [v0, d];
                            let mut f = d;
                            f.mul_assign(w3);
                            f.add_assign(&v0);
                            base_buffers[poly_idx].write(pos, f);
                            grid[9 * (j >> 2) + 3 * ((j >> 1) & 1) + (j & 1)] = f;
                        }
                        fill_inf_cells(grid);
                    }
                    for (poly_idx, src) in ext_field_inputs.iter().enumerate() {
                        let scratch_pairs = &mut pairs[num_base + poly_idx];
                        let grid = &mut grids[num_base + poly_idx];
                        for j in 0..8usize {
                            let pos = row
                                + (j >> 2) * corner_strides[0]
                                + ((j >> 1) & 1) * corner_strides[1]
                                + (j & 1) * corner_strides[2];
                            let (v0, v1) = read_ext_and_fold_pair(
                                src,
                                precomputed_eq_prefix,
                                fold_stride,
                                pos,
                                pos + half,
                            );
                            let mut d = v1;
                            d.sub_assign(&v0);
                            scratch_pairs[j] = [v0, d];
                            let mut f = d;
                            f.mul_assign(w3);
                            f.add_assign(&v0);
                            ext_buffers[poly_idx].write(pos, f);
                            grid[9 * (j >> 2) + 3 * ((j >> 1) & 1) + (j & 1)] = f;
                        }
                        fill_inf_cells(grid);
                    }

                    // round-3 accumulator: one 2-cell evaluation per corner
                    for j in 0..8usize {
                        eval2 = [E::ZERO; 2];
                        for step in description.folded_evaluation_steps.iter() {
                            match *step {
                                FoldedEvaluationStep::Quadratic {
                                    scratch_idx_a,
                                    scratch_idx_b,
                                    coeff_idx,
                                } => {
                                    let coeff = description.constants[coeff_idx as usize];
                                    evaluate_quadratic_ext(
                                        &mut eval2,
                                        &pairs[scratch_idx_a as usize][j],
                                        &pairs[scratch_idx_b as usize][j],
                                        &coeff,
                                    );
                                }
                                FoldedEvaluationStep::Linear {
                                    scratch_idx,
                                    coeff_idx,
                                } => {
                                    let coeff = description.constants[coeff_idx as usize];
                                    let mut t = coeff;
                                    t.mul_assign(&pairs[scratch_idx as usize][j][0]);
                                    eval2[0].add_assign(&t);
                                }
                            }
                        }
                        eval2[0].add_assign(&description.total_additive_constant);
                        let mut weight = eq_mid[j];
                        weight.mul_assign(&eq_suffix[row]);
                        let mut t = eval2[0];
                        t.mul_assign(&weight);
                        acc2[0].add_assign(&t);
                        let mut t = eval2[1];
                        t.mul_assign(&weight);
                        acc2[1].add_assign(&t);
                    }

                    // rounds 4-6 accumulator: one 27-cell evaluation on the
                    // freshly folded grids
                    eval27 = [E::ZERO; 27];
                    for step in description.folded_evaluation_steps.iter() {
                        match *step {
                            FoldedEvaluationStep::Quadratic {
                                scratch_idx_a,
                                scratch_idx_b,
                                coeff_idx,
                            } => {
                                let coeff = description.constants[coeff_idx as usize];
                                evaluate_quadratic_ext(
                                    &mut eval27,
                                    &grids[scratch_idx_a as usize],
                                    &grids[scratch_idx_b as usize],
                                    &coeff,
                                );
                            }
                            FoldedEvaluationStep::Linear {
                                scratch_idx,
                                coeff_idx,
                            } => {
                                let coeff = description.constants[coeff_idx as usize];
                                evaluate_linear_ext(
                                    &mut eval27,
                                    &grids[scratch_idx as usize],
                                    &coeff,
                                );
                            }
                        }
                    }
                    // additive constant on the binary cells
                    for i in 0..2 {
                        let offset = 9 * i;
                        for jj in 0..2 {
                            let offset = offset + 3 * jj;
                            for kk in 0..2 {
                                eval27[offset + kk]
                                    .add_assign(&description.total_additive_constant);
                            }
                        }
                    }
                    accumulate_scaled(&mut acc27, &eval27, &eq_suffix[row]);
                }

                *dst = (acc2, acc27);
            });
        }
    });

    let mut acc2 = [E::ZERO; 2];
    let mut acc27 = [E::ZERO; 27];
    for (a2, a27) in results.into_iter() {
        acc2[0].add_assign(&a2[0]);
        acc2[1].add_assign(&a2[1]);
        for i in 0..27 {
            acc27[i].add_assign(&a27[i]);
        }
    }

    (acc2, acc27)
}

/// Fill the 19 infinity cells of a 27-grid from its 8 binary cells.
#[inline(always)]
fn fill_inf_cells<E: Field>(dst: &mut [E; 27]) {
    for x0 in 0..2 {
        let base = 9 * x0;
        for x1 in 0..2 {
            let off = base + 3 * x1;
            dst[off + 2] = interpolate_at_inf_from_0_1_basis(dst[off], dst[off + 1]);
        }
        for x2 in 0..3 {
            dst[base + 6 + x2] =
                interpolate_at_inf_from_0_1_basis(dst[base + x2], dst[base + 3 + x2]);
        }
    }
    for x1 in 0..3 {
        let off = 3 * x1;
        for x2 in 0..3 {
            dst[18 + off + x2] =
                interpolate_at_inf_from_0_1_basis(dst[off + x2], dst[9 + off + x2]);
        }
    }
}
