//! Intermediate WHIR oracle committed BY COEFFICIENT.
//!
//! The folded polynomial's `E::DEGREE` base-field limb columns are LDE'd
//! independently through the backend's base-column pipeline (the one the base
//! commits use), and the leaves are re-assembled into extension elements while
//! the tree is hashed, so the commitment — tree, leaf order, leaf encoding —
//! is byte-identical to the extension-field oracle
//! ([`ContinuousExtensionOracleForLDE`]).
//!
//! Storage geometry: the backend's base LDE is fastest at ONE column length
//! `2n` ([`Backend::by_coefficient_lde_len`]: the strided 2^24 pipeline), so a
//! folded polynomial of `n` values is committed as `2n` hypercube evaluations
//! — the values DUPLICATED, i.e. the multilinear extension in one more variable
//! that ignores it, which is the same univariate polynomial with zero top
//! coefficients — at half the LDE factor: the same `n * lde_factor` codeword
//! points, grouped as `lde_factor / 2` STORAGE cosets of `2n` points instead of
//! `lde_factor` LOGICAL cosets of `n`. With `e = c + lde_factor * i` the point
//! index of logical coset `c`, position `i` (the codeword's coset offsets are
//! the powers of the `n * lde_factor`-th root): storage coset
//! `c mod (lde_factor / 2)`, storage position `2 * i + c div (lde_factor / 2)`
//! — a logical coset is the even or the odd half of a storage coset. Leaves keep
//! the LOGICAL structure (a coset of the folding subgroup inside one logical
//! coset), so the tree index, the leaf contents and the leaf conversion (the
//! same per-logical-coset root inverses) are exactly the extension-field
//! oracle's.
#[allow(unused_imports)]
use super::ContinuousExtensionOracleForLDE;
use super::{offsets_vec_for_leaf_construction, ExtensionFieldQuery};
use crate::allocation_pool::{AllocationPool, Buffer, ColumnLayout};
use crate::gkr::prover::backend::{
    coset_offsets, Backend, ExtCoeffConversion, LeafConversionHandle,
};
use crate::gkr::prover::stages::commitment_utils::ColumnMajorCosetBoundTracePart;
use crate::merkle_trees::{ColumnMajorMerkleTreeConstructor, CosetLeafAccessor};
use crate::utils::extension_field_into_base_coeffs;
use fft::{batch_inverse_inplace, bitreverse_index};
use field::{Field, FieldExtension, FixedArrayConvertible, PrimeField, TwoAdicField};
use std::sync::Arc;
use worker::Worker;

/// Leaf accessor of ONE logical coset stored as the `parity` half of a
/// storage coset's limb columns: gathers the leaf's evaluations (assembled
/// into `E`) in the tree's leaf order and converts them through the
/// oracle-wide [`ExtCoeffConversion`] — what the tree hashes and the
/// queries return ([`CosetLeafAccessor`]).
pub struct ByCoefficientLeaves<'a, F, E, C: ?Sized> {
    conv: &'a C,
    /// The storage coset's limb columns (raw storage, addressed via `layout`).
    limbs: Vec<&'a [F]>,
    layout: ColumnLayout,
    parity: usize,
    /// Leaf gather offsets inside the logical coset.
    offsets: &'a [usize],
    offset_inv: F,
    num_leaves: usize,
    /// Four consecutive leaves gather as aligned 8-lane vectors (BabyBear
    /// Ext4 over BabyBear, AVX2, 4-aligned leaf offsets).
    vector4: bool,
    _marker: core::marker::PhantomData<E>,
}

impl<'a, F, E, C> ByCoefficientLeaves<'a, F, E, C>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    C: ExtCoeffConversion<F, E> + ?Sized,
    [(); E::DEGREE]: Sized,
{
    pub fn new(
        conv: &'a C,
        storage_coset: &'a [ColumnMajorCosetBoundTracePart<F, F>],
        parity: usize,
        offsets: &'a [usize],
        offset_inv: F,
        num_leaves: usize,
    ) -> Self {
        assert_eq!(storage_coset.len(), E::DEGREE);
        let layout = storage_coset[0].layout;
        let storage_len = storage_coset[0].len();
        for part in storage_coset.iter() {
            assert_eq!(part.layout, layout);
            assert_eq!(part.len(), storage_len);
        }
        assert_eq!(storage_len, 2 * num_leaves * offsets.len());
        assert!(parity < 2);
        let limbs: Vec<&'a [F]> = storage_coset.iter().map(|part| &part.column[..]).collect();
        let vector4 = Self::vector4_applicable(&limbs, offsets, num_leaves);
        Self {
            conv,
            limbs,
            layout,
            parity,
            offsets,
            offset_inv,
            num_leaves,
            vector4,
            _marker: core::marker::PhantomData,
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn vector4_applicable(limbs: &[&'a [F]], offsets: &[usize], num_leaves: usize) -> bool {
        use core::any::TypeId;
        let _ = limbs;
        TypeId::of::<E>() == TypeId::of::<crate::field::baby_bear::ext4::BabyBearExt4>()
            && TypeId::of::<F>() == TypeId::of::<crate::field::baby_bear::base::BabyBearField>()
            && num_leaves % 4 == 0
            && offsets.iter().all(|&o| o % 4 == 0)
            && is_x86_feature_detected!("avx2")
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn vector4_applicable(_limbs: &[&'a [F]], _offsets: &[usize], _num_leaves: usize) -> bool {
        false
    }

    /// Leaves `first .. first + 4` (`first % 4 == 0`) of a BabyBear Ext4
    /// oracle: per offset and limb ONE 8-lane load covers the four leaves'
    /// storage positions `2(off + first) + parity + {0, 2, 4, 6}` (both
    /// parities share those 8 lanes, the span never crosses a padded block),
    /// compacted to the wanted parity and transposed into four Ext4 values
    /// (`[c0.c0, c0.c1, c1.c0, c1.c1]` is the memory order of
    /// `BabyBearExt4` and of its `into_coeffs`).
    ///
    /// `slot_major`: `out[4k + w]` (slot `k` of leaf `w`, one contiguous
    /// 64-byte store per slot); otherwise leaf-major `out[w * vpl + k]`.
    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn gather_leaves4_avx2(&self, first: usize, out: &mut [E], slot_major: bool) {
        use core::arch::x86_64::*;
        let vpl = self.offsets.len();
        debug_assert_eq!(first % 4, 0);
        debug_assert!(first + 4 <= self.num_leaves);
        debug_assert_eq!(out.len(), 4 * vpl);
        let out_ptr = out.as_mut_ptr() as *mut u32;
        let (s0, s1, s2, s3, step) = if slot_major {
            (0usize, 4usize, 8usize, 12usize, 16usize)
        } else {
            (0usize, vpl * 4, 2 * vpl * 4, 3 * vpl * 4, 4usize)
        };
        let l0 = self.limbs[0].as_ptr() as *const u32;
        let l1 = self.limbs[1].as_ptr() as *const u32;
        let l2 = self.limbs[2].as_ptr() as *const u32;
        let l3 = self.limbs[3].as_ptr() as *const u32;
        let sel = if self.parity == 0 {
            _mm256_setr_epi32(0, 2, 4, 6, 0, 0, 0, 0)
        } else {
            _mm256_setr_epi32(1, 3, 5, 7, 0, 0, 0, 0)
        };
        for (k, &off) in self.offsets.iter().enumerate() {
            let p = 2 * (off + first);
            let idx = match self.layout {
                ColumnLayout::Contiguous => p,
                ColumnLayout::PaddedBlocks(g) => g.index(p),
            };
            let a = _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(
                _mm256_loadu_si256(l0.add(idx) as *const __m256i),
                sel,
            ));
            let b = _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(
                _mm256_loadu_si256(l1.add(idx) as *const __m256i),
                sel,
            ));
            let c = _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(
                _mm256_loadu_si256(l2.add(idx) as *const __m256i),
                sel,
            ));
            let d = _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(
                _mm256_loadu_si256(l3.add(idx) as *const __m256i),
                sel,
            ));
            // 4x4 transpose: rows are limbs, columns leaves
            let t0 = _mm_unpacklo_epi32(a, b);
            let t1 = _mm_unpackhi_epi32(a, b);
            let t2 = _mm_unpacklo_epi32(c, d);
            let t3 = _mm_unpackhi_epi32(c, d);
            let e0 = _mm_unpacklo_epi64(t0, t2);
            let e1 = _mm_unpackhi_epi64(t0, t2);
            let e2 = _mm_unpacklo_epi64(t1, t3);
            let e3 = _mm_unpackhi_epi64(t1, t3);
            let base = out_ptr.add(k * step);
            _mm_storeu_si128(base.add(s0) as *mut __m128i, e0);
            _mm_storeu_si128(base.add(s1) as *mut __m128i, e1);
            _mm_storeu_si128(base.add(s2) as *mut __m128i, e2);
            _mm_storeu_si128(base.add(s3) as *mut __m128i, e3);
        }
    }

    /// The leaf's EVALUATIONS in leaf order (no conversion).
    #[inline(always)]
    pub fn gather_leaf(&self, leaf_index: usize, out: &mut [E]) {
        debug_assert!(leaf_index < self.num_leaves);
        debug_assert_eq!(out.len(), self.offsets.len());
        let mut coeffs = [F::ZERO; E::DEGREE];
        match self.layout {
            ColumnLayout::Contiguous => {
                for (o, &off) in out.iter_mut().zip(self.offsets.iter()) {
                    let p = 2 * (off + leaf_index) + self.parity;
                    for (c, limb) in coeffs.iter_mut().zip(self.limbs.iter()) {
                        *c = limb[p];
                    }
                    *o =
                        E::from_coeffs(<E::Coeffs as FixedArrayConvertible<F>>::from_array(coeffs));
                }
            }
            ColumnLayout::PaddedBlocks(geo) => {
                for (o, &off) in out.iter_mut().zip(self.offsets.iter()) {
                    let p = geo.index(2 * (off + leaf_index) + self.parity);
                    for (c, limb) in coeffs.iter_mut().zip(self.limbs.iter()) {
                        *c = limb[p];
                    }
                    *o =
                        E::from_coeffs(<E::Coeffs as FixedArrayConvertible<F>>::from_array(coeffs));
                }
            }
        }
    }
}

impl<'a, F, E, C> CosetLeafAccessor<E> for ByCoefficientLeaves<'a, F, E, C>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    C: ExtCoeffConversion<F, E> + ?Sized,
    [(); E::DEGREE]: Sized,
{
    fn num_leaves(&self) -> usize {
        self.num_leaves
    }
    fn values_per_leaf(&self) -> usize {
        self.offsets.len()
    }
    #[inline(always)]
    fn leaf_into(&self, leaf_index: usize, out: &mut [E]) {
        self.gather_leaf(leaf_index, out);
        self.conv
            .convert_gathered_leaf(self.offset_inv, leaf_index, out);
    }
    #[inline(always)]
    fn leaves_into(&self, first_leaf: usize, count: usize, out: &mut [E]) {
        let vpl = self.offsets.len();
        #[cfg(target_arch = "x86_64")]
        if count == 4 && self.vector4 && first_leaf % 4 == 0 {
            unsafe { self.gather_leaves4_avx2(first_leaf, &mut out[..4 * vpl], false) };
            self.conv
                .convert_gathered_leaves(self.offset_inv, first_leaf, count, out);
            return;
        }
        for (w, chunk) in out[..count * vpl].chunks_exact_mut(vpl).enumerate() {
            self.gather_leaf(first_leaf + w, chunk);
        }
        self.conv
            .convert_gathered_leaves(self.offset_inv, first_leaf, count, out);
    }
    #[inline(always)]
    fn leaves_into_slot_major(&self, first_leaf: usize, count: usize, out: &mut [E]) -> bool {
        #[cfg(target_arch = "x86_64")]
        if count == 4 && self.vector4 && first_leaf % 4 == 0 {
            let vpl = self.offsets.len();
            unsafe { self.gather_leaves4_avx2(first_leaf, &mut out[..4 * vpl], true) };
            self.conv
                .convert_gathered_block(self.offset_inv, first_leaf, count, out);
            return true;
        }
        let _ = (first_leaf, count, out);
        false
    }
}

/// The by-coefficient intermediate oracle: `lde_factor / 2` storage cosets
/// of `E::DEGREE` base columns (evaluation form, any column layout) plus the
/// tree; leaves are assembled and converted on access.
pub struct ByCoefficientExtOracle<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    /// `columns[storage_coset][limb]`, each `2 * 2^trace_len_log2` points.
    pub columns: Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>>,
    /// log2 of a LOGICAL coset (the folded polynomial size).
    pub trace_len_log2: usize,
    /// Logical cosets (the LDE factor).
    pub num_cosets: usize,
    pub values_per_leaf: usize,
    pub tree: T,
    /// The leaf encoding the tree committed to.
    pub conv: LeafConversionHandle<F, E>,
    /// Inverses of the LOGICAL coset offsets (natural coset order).
    pub coset_offsets_inv: Vec<F>,
    /// Leaf gather offsets inside a logical coset (tree leaf order).
    offsets: Vec<usize>,
}

impl<
        F: PrimeField + TwoAdicField,
        E: FieldExtension<F> + Field,
        T: ColumnMajorMerkleTreeConstructor<F>,
    > ByCoefficientExtOracle<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    pub fn num_cosets(&self) -> usize {
        self.num_cosets
    }

    fn num_leaves_per_coset(&self) -> usize {
        (1usize << self.trace_len_log2) / self.values_per_leaf
    }

    /// The accessor of logical coset `coset_index`.
    fn accessor(
        &self,
        coset_index: usize,
    ) -> ByCoefficientLeaves<'_, F, E, dyn ExtCoeffConversion<F, E>> {
        let storage_cosets = self.columns.len();
        ByCoefficientLeaves::new(
            &*self.conv,
            &self.columns[coset_index % storage_cosets],
            coset_index / storage_cosets,
            &self.offsets,
            self.coset_offsets_inv[coset_index],
            self.num_leaves_per_coset(),
        )
    }

    /// The leaf at folded index `index` as stored: EVALUATIONS in leaf order
    /// (no conversion, no Merkle proof).
    pub(crate) fn leaf_evaluations(&self, index: usize) -> Vec<E> {
        let coset_index = index & (self.num_cosets - 1);
        let internal_index = index / self.num_cosets;
        let mut values = vec![E::ZERO; self.values_per_leaf];
        self.accessor(coset_index)
            .gather_leaf(internal_index, &mut values);
        values
    }

    /// Identical to [`ContinuousExtensionOracleForLDE::query_for_folded_index`].
    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<E>, ExtensionFieldQuery<F, E, T>) {
        let num_cosets = self.num_cosets;
        let coset_index = index & (num_cosets - 1);
        let internal_index = index / num_cosets;
        let coset_tree_size = self.num_leaves_per_coset();
        let mut values = vec![E::ZERO; self.values_per_leaf];
        self.accessor(coset_index)
            .leaf_into(internal_index, &mut values);

        let coset_dest_index = bitreverse_index(coset_index, num_cosets.trailing_zeros());
        let tree_index = coset_dest_index * coset_tree_size + internal_index;

        let (_leaf_hash, path) = self.tree.get_proof(tree_index);
        let query = ExtensionFieldQuery {
            index: tree_index,
            leaf_values_concatenated: values.clone(),
            path,
            _marker: core::marker::PhantomData,
        };
        (coset_index, values, query)
    }

    /// Give the pooled codeword columns back.
    pub fn release_into(self, pool: &dyn AllocationPool<F, E>) {
        for coset in self.columns.into_iter() {
            for part in coset.into_iter() {
                if let Ok(column) = Arc::try_unwrap(part.column) {
                    column.release_base(pool);
                }
            }
        }
    }
}

/// Commit `evaluation_form` (the folded polynomial's hypercube evaluations,
/// `n` values) with `lde_factor` logical cosets and `values_per_leaf` values
/// per leaf, by coefficient: the limb columns duplicated to `2n` go through
/// the backend's base-column LDE at `lde_factor / 2`, the tree is hashed
/// over assembled + converted leaves. Returns the oracle and the (LDE, tree)
/// wall times.
pub(crate) fn commit_by_coefficient<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    B: Backend<F, E>,
>(
    evaluation_form: &[E],
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
    backend: &B,
    twiddles: &B::TwiddleSet,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> (
    ByCoefficientExtOracle<F, E, T>,
    std::time::Duration,
    std::time::Duration,
)
where
    [(); E::DEGREE]: Sized,
{
    let n = evaluation_form.len();
    assert!(n.is_power_of_two());
    assert!(lde_factor.is_power_of_two() && lde_factor >= 2);
    assert!(values_per_leaf.is_power_of_two() && values_per_leaf <= n);
    let storage_n = 2 * n;
    let storage_lde = lde_factor / 2;

    let t_lde = std::time::Instant::now();
    // the limb columns, duplicated to 2n
    let mut limbs: Vec<Buffer<F>> = (0..E::DEGREE)
        .map(|_| pool.alloc_base(storage_n, ColumnLayout::Contiguous))
        .collect();
    {
        let ptrs: Vec<usize> = limbs.iter_mut().map(|b| b.as_mut_ptr() as usize).collect();
        worker.scope(n, |scope, geometry| {
            for chunk_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(chunk_idx);
                let size = geometry.get_chunk_size(chunk_idx);
                let ptrs = &ptrs;
                let is_last = chunk_idx == geometry.len() - 1;
                Worker::smart_spawn(scope, is_last, move |_| {
                    for i in start..start + size {
                        let coeffs = extension_field_into_base_coeffs::<F, E>(evaluation_form[i]);
                        for (l, c) in coeffs.iter().enumerate() {
                            let p = ptrs[l] as *mut F;
                            unsafe {
                                p.add(i).write(*c);
                                p.add(i + n).write(*c);
                            }
                        }
                    }
                });
            }
        });
    }
    let columns = {
        let limb_slices: Vec<&[F]> = limbs
            .iter()
            .map(|b| unsafe { b.as_ref_assume_init() })
            .collect();
        backend.lde_multiple_polys_from_hypercubes(
            &limb_slices,
            twiddles,
            storage_lde,
            pool,
            worker,
        )
    };
    for b in limbs.into_iter() {
        pool.give_base(b);
    }
    let t_lde = t_lde.elapsed();
    assert_eq!(columns.len(), storage_lde);
    debug_assert!(columns
        .iter()
        .zip(coset_offsets::<F>(storage_n, storage_lde).iter())
        .all(|(coset, offset)| coset.iter().all(|part| part.offset == *offset)));

    let t_tree = std::time::Instant::now();
    let conv = backend.ext_coeff_conv(n, values_per_leaf);
    let coset_offsets = coset_offsets::<F>(n, lde_factor);
    let mut coset_offsets_inv = coset_offsets.clone();
    let mut inv_scratch = vec![F::ZERO; lde_factor];
    batch_inverse_inplace(&mut coset_offsets_inv, &mut inv_scratch);
    let offsets = offsets_vec_for_leaf_construction(n, values_per_leaf);
    let num_leaves = n / values_per_leaf;
    let tree = {
        let accessors: Vec<[ByCoefficientLeaves<'_, F, E, B::ExtCoeffConv>; 1]> = (0..lde_factor)
            .map(|c| {
                [ByCoefficientLeaves::new(
                    &conv,
                    &columns[c % storage_lde],
                    c / storage_lde,
                    &offsets,
                    coset_offsets_inv[c],
                    num_leaves,
                )]
            })
            .collect();
        let refs: Vec<&[ByCoefficientLeaves<'_, F, E, B::ExtCoeffConv>]> =
            accessors.iter().map(|a| &a[..]).collect();
        T::construct_from_leaf_accessors::<E, _>(&refs[..], tree_cap_size, true, false, worker)
    };
    let t_tree = t_tree.elapsed();

    let oracle = ByCoefficientExtOracle {
        columns,
        trace_len_log2: n.trailing_zeros() as usize,
        num_cosets: lde_factor,
        values_per_leaf,
        tree,
        conv: LeafConversionHandle(Arc::new(conv)),
        coset_offsets_inv,
        offsets,
    };
    (oracle, t_lde, t_tree)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocation_pool::GenericAllocationPool;
    use crate::gkr::prover::backend::NaiveBackend;
    use crate::gkr::whir::commit_single_ext_poly_continuous;
    use crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs;
    use crate::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
    use crate::merkle_trees::PathQueryable;
    use field::Rand;

    type F = crate::field::baby_bear::base::BabyBearField;
    type E = crate::field::baby_bear::ext4::BabyBearExt4;
    type Tree = Blake2sU32MerkleTreeWithCap;

    /// The by-coefficient oracle must be byte-identical to the extension-field
    /// continuous oracle of the same backend: same raw leaves (the LDE values),
    /// same converted leaves and paths (the conversion + tree), same cap.
    fn check_parity<B: Backend<F, E>>(
        backend: &B,
        pool: &dyn AllocationPool<F, E>,
        poly_log2: usize,
        lde_factor: usize,
        values_per_leaf: usize,
        worker: &Worker,
    ) {
        let poly_size = 1usize << poly_log2;
        let mut rng = rand::thread_rng();
        let evals: Vec<E> = (0..poly_size)
            .map(|_| E::random_element(&mut rng))
            .collect();
        let mut monomial = evals.clone();
        multivariate_hypercube_evals_into_coeffs(&mut monomial, poly_log2 as u32);
        let twiddles = backend.make_twiddles(2 * poly_size, worker);
        let (buffer, offsets) = backend.lde_ext_poly_from_monomial_form_continuous(
            &monomial, &twiddles, lde_factor, pool, worker,
        );
        let reference = commit_single_ext_poly_continuous::<F, E, Tree, B>(
            buffer,
            offsets,
            values_per_leaf,
            4,
            backend,
            worker,
        );
        let (by_coeff, _, _) = commit_by_coefficient::<F, E, Tree, B>(
            &evals,
            lde_factor,
            values_per_leaf,
            4,
            backend,
            &twiddles,
            pool,
            worker,
        );
        let num_leaves = lde_factor * poly_size / values_per_leaf;
        let mut indices = vec![
            0usize,
            1,
            7,
            num_leaves / 3,
            num_leaves / 2 + 5,
            num_leaves - 1,
        ];
        for c in 0..lde_factor {
            indices.push(c + lde_factor * (num_leaves / lde_factor / 5));
        }
        for &index in indices.iter() {
            let label = format!(
                "2^{poly_log2} x{lde_factor} vpl {values_per_leaf}: leaf {index} (coset {}, internal {})",
                index % lde_factor,
                index / lde_factor
            );
            if !reference.leaves_in_coefficient_form {
                let a = reference.leaf_evaluations(index);
                let b = by_coeff.leaf_evaluations(index);
                if a != b {
                    let k = a.iter().zip(b.iter()).position(|(x, y)| x != y).unwrap();
                    panic!(
                        "{label}: RAW values differ first at position {k}: {:?} vs {:?}",
                        a[k], b[k]
                    );
                }
            }
            let (ca, a, qa) = reference.query_for_folded_index(index);
            let (cb, b, qb) = by_coeff.query_for_folded_index(index);
            assert_eq!(ca, cb, "{label}: coset");
            if a != b {
                let k = a.iter().zip(b.iter()).position(|(x, y)| x != y).unwrap();
                panic!(
                    "{label}: CONVERTED values differ first at position {k}: {:?} vs {:?}",
                    a[k], b[k]
                );
            }
            assert_eq!(qa.index, qb.index, "{label}: tree index");
            assert_eq!(
                qa.leaf_values_concatenated, qb.leaf_values_concatenated,
                "{label}"
            );
            assert_eq!(qa.path, qb.path, "{label}: path");
        }
        assert_eq!(
            reference.tree.get_cap(),
            by_coeff.tree.get_cap(),
            "cap 2^{poly_log2} x{lde_factor} vpl {values_per_leaf}"
        );
        by_coeff.release_into(pool);
    }

    #[test]
    fn by_coefficient_oracle_matches_continuous() {
        let worker = Worker::new_with_num_threads(4);
        let pool = GenericAllocationPool::<F, E>::new();
        for (poly_log2, lde_factor, values_per_leaf) in
            [(10usize, 16usize, 32usize), (11, 8, 32), (9, 4, 16)]
        {
            check_parity(
                &NaiveBackend,
                &pool,
                poly_log2,
                lde_factor,
                values_per_leaf,
                &worker,
            );
        }
    }

    /// The AVX2 backend (its LDE kernels and its gathered-leaf conversion),
    /// contiguous storage, both LDE plans (flat grid below 2^20, every coset
    /// on all threads from 2^20 up).
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn by_coefficient_oracle_matches_continuous_avx2() {
        let worker = Worker::new_with_num_threads(8);
        let pool = crate::allocation_pool::X86BabyBearAllocationPool::new();
        let backend = crate::gkr::prover::backend::BabyBearAvx2WorkStealingBackend;
        for (poly_log2, lde_factor, values_per_leaf) in
            [(12usize, 16usize, 32usize), (11, 8, 16), (20, 16, 32)]
        {
            check_parity(
                &backend,
                &pool,
                poly_log2,
                lde_factor,
                values_per_leaf,
                &worker,
            );
        }
    }

    /// The production shape through the AVX-512 strided pipeline (block-padded
    /// storage): 2^23 values, 16 logical cosets = 8 strided 2^24 cosets.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[test]
    fn by_coefficient_oracle_matches_continuous_strided() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let worker = Worker::new();
        let pool = crate::allocation_pool::X86BabyBearAllocationPool::new();
        let backend = crate::gkr::prover::backend::BabyBearAvx512WorkStealingBackend::new(true);
        assert_eq!(backend.by_coefficient_lde_len(), Some(1 << 24));
        check_parity(&backend, &pool, 23, 16, 32, &worker);
    }
}
