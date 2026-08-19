//! Compute backend for the heavy polynomial operations of the IN-MEMORY prover
//! path: multi-column LDEs for the base commitments, per-coset LDEs of packed
//! monomials, the extension-field LDE behind each materialized intermediate WHIR
//! oracle, hypercube→monomial transforms, and the batching IFFT in `whir_fold`.
//!
//! The [`Backend`] trait pins the exact input/output contracts of the historical
//! free functions; [`NaiveBackend`] delegates to them unchanged, so it works for
//! every `<F, E>` pair and produces byte-identical commitments/proofs.
//! Alternative implementations may re-schedule the work (e.g. distribute
//! poly×coset tasks over a work-stealing pool when few polynomials meet a large
//! LDE factor) or swap in faster FFT kernels — the contract is that the OUTPUT
//! values are identical; only the execution strategy may differ.

use super::commitment_utils::{
    compute_column_major_lde_from_monomial_form,
    compute_column_major_monomial_form_from_main_domain_owned,
    lde_multiple_polys_parallel_from_hypercubes, lde_packed_monomials_into_cosets,
    pack_polys_parallel_from_hypercubes_to_monomials, ColumnMajorCosetBoundTracePart,
};
use crate::gkr::whir::ColumnMajorBaseOracleForCoset;
use fft::Twiddles;
// Only reachable from the aarch64/NEON backend items below; on every other
// target `DefaultBabyBearBackend` is the generic WorkStealingBackend and these
// names go unused. (The test module has its own import.)
#[cfg(target_arch = "aarch64")]
use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use field::{Field, FieldExtension, PrimeField, Proth120, TwoAdicField};
use std::alloc::Global;
use std::sync::Arc;
use worker::Worker;

mod proth120;
pub use proth120::Proth120WorkStealingLazyBackend;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::BabyBearNeonWorkStealingBackend;

mod naive;
pub use naive::NaiveBackend;

mod work_stealing;
pub use work_stealing::WorkStealingBackend;

/// In-place conversion of a materialized intermediate-oracle coset from
/// evaluation form to the PRODUCTION leaf encoding (multilinear-coefficient
/// leaves by default; the identity under the `eval_leaves` feature). An
/// ASSOCIATED TYPE of [`Backend`], so the conversion's tables and scratch
/// buffers stay implementation-private and alternative backends may supply
/// specialized (e.g. vectorized) conversions later.
pub trait ExtCoeffConversion<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>:
    Send + Sync
{
    /// Worker-parallel conversion of one coset (`column` in natural order,
    /// with LDE `offset`).
    fn apply(&self, column: &mut [E], offset: F, worker: &Worker);
    /// Fully serial variant for flat per-coset task grids (bit-identical to
    /// [`Self::apply`]).
    fn apply_serial(&self, column: &mut [E], offset: F);
}

/// The standard conversion used by every current backend: wraps the
/// coefficient-form context (or nothing when `eval_leaves` keeps raw
/// evaluations committed). The leaf-encoding conditional compilation lives
/// entirely INSIDE this type.
pub struct StandardExtCoeffConv<F: PrimeField + TwoAdicField> {
    #[cfg(not(feature = "eval_leaves"))]
    ctx: crate::gkr::whir::ExtCoeffConvCtx<F>,
    #[cfg(feature = "eval_leaves")]
    _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField + TwoAdicField> StandardExtCoeffConv<F> {
    pub fn new(coset_len: usize, values_per_leaf: usize) -> Self {
        #[cfg(not(feature = "eval_leaves"))]
        {
            Self {
                ctx: crate::gkr::whir::ExtCoeffConvCtx::new(coset_len, values_per_leaf),
            }
        }
        #[cfg(feature = "eval_leaves")]
        {
            let _ = (coset_len, values_per_leaf);
            Self {
                _marker: core::marker::PhantomData,
            }
        }
    }
}

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> ExtCoeffConversion<F, E>
    for StandardExtCoeffConv<F>
{
    fn apply(&self, column: &mut [E], offset: F, worker: &Worker) {
        #[cfg(not(feature = "eval_leaves"))]
        self.ctx.apply(column, offset, worker);
        #[cfg(feature = "eval_leaves")]
        {
            let _ = (column, offset, worker);
        }
    }

    fn apply_serial(&self, column: &mut [E], offset: F) {
        #[cfg(not(feature = "eval_leaves"))]
        self.ctx.apply_serial(column, offset);
        #[cfg(feature = "eval_leaves")]
        {
            let _ = (column, offset);
        }
    }
}

/// The compute backend of the in-memory prover path. `F` is the base (proof)
/// field, `E` the extension field the folded WHIR polynomials live in (equal to
/// `F` for large-field proofs such as Proth120).
///
/// The prover is parameterized by a SINGLE `B: Backend<F, E>` — it cannot
/// re-instantiate the same type at `Backend<F, F>` for the base-field stages —
/// so operations needed for both element types exist as F-typed and E-typed
/// twins in this one trait (e.g. [`Self::lde_base_poly_from_monomial_form`] /
/// [`Self::lde_ext_poly_from_monomial_form`]).
///
/// Threading: implementations must confine all parallelism to the passed
/// [`Worker`] (its geometry-based `scope` or its owned rayon pool via
/// `worker.pool.install(..)`) — never rayon's GLOBAL pool — so the caller's
/// thread budget is always respected (important on heterogeneous-core hosts and
/// in tests pinning specific thread counts).
///
/// Every method mirrors a historical free function: same inputs, same outputs
/// (bit-for-bit — proofs must not depend on the backend choice).
pub trait Backend<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>: Send + Sync {
    /// LDE a batch of base-field columns given on the boolean hypercube into all
    /// `lde_factor` cosets. `result[coset][column]` holds natural-order coset
    /// evaluations with the coset offset attached. Mirrors
    /// `lde_multiple_polys_parallel_from_hypercubes`.
    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[F]],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>>;

    /// LDE a batch of base-field polynomials given as multilinear monomial
    /// coefficients (normal order, all the same power-of-two length) into all
    /// `lde_factor` cosets, CONSUMING the monomial forms. `result[coset]` holds
    /// one natural-order column per input polynomial plus the coset offset.
    /// Mirrors the per-coset loop of the packed in-memory committers.
    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<F>>,
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<F>>;

    /// LDE ONE extension-field polynomial (multilinear monomial coefficients,
    /// normal order) into all `lde_factor` cosets — the RS codeword of a
    /// materialized intermediate WHIR oracle. Mirrors
    /// `compute_column_major_lde_from_monomial_form(.., Some(worker))`.
    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[E],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[E]>, F)>;

    /// Base-field twin of [`Self::lde_ext_poly_from_monomial_form`]: LDE one
    /// F-valued polynomial (monomial coefficients, normal order) into all
    /// `lde_factor` cosets. Duplicated because the prover holds a single
    /// `Backend<F, E>` and cannot use the same type as `Backend<F, F>`.
    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[F],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[F]>, F)>;

    /// Pack groups of `2^pack_log2` hypercube columns into single multilinears
    /// and return their monomial coefficient forms. Mirrors
    /// `pack_polys_parallel_from_hypercubes_to_monomials`.
    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[F]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<F>>;

    /// Main-domain (coset 0) evaluations → multilinear monomial coefficients
    /// (inverse NTT + 1/N + bit-reversal), consuming the input. Used for the
    /// batched proximity polynomial in `whir_fold` — an O(1)-per-proof
    /// transformation of a full trace-length Ext poly, so implementations
    /// should put ALL worker threads on it. Mirrors
    /// `compute_column_major_monomial_form_from_main_domain_owned`.
    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<E>,
        twiddles: &Twiddles<F, Global>,
        worker: &Worker,
    ) -> Vec<E>;

    /// Monomial coefficients → boolean-hypercube evaluations (the ADD Mobius
    /// transform) followed by the bit-reversal — the second O(1)-per-proof
    /// transformation of the batched Ext poly in `whir_fold`; implementations
    /// should put ALL worker threads on it. Mirrors
    /// `parallel_multivariate_coeffs_into_hypercube_evals` + bitrev.
    fn hypercube_evals_from_monomial_form(&self, monomial_form: Vec<E>, worker: &Worker) -> Vec<E>;

    /// Accumulate one WHIR round's equality-poly contributions into the
    /// (already folded) eq poly: `dst[i] += ch_ood * eq(i, ood_point)` followed
    /// by `dst[i] += ch_q * eq(i, query_point)` for every in-domain sample, in
    /// sample order — an O(1)-per-round pass over a full-size Ext poly with
    /// `~64` samples, so implementations should batch samples and put ALL
    /// worker threads on it. Mirrors `update_eq_poly_reference`.
    fn update_eq_poly(
        &self,
        eq_poly: &mut [E],
        ood_samples: &[(E, E)],
        in_domain_samples: &[(F, E)],
        worker: &Worker,
    );

    /// Leaf-encoding conversion context for materialized intermediate WHIR
    /// oracles — built once per oracle commit (its tables are coset-length
    /// sized) and shared across all that oracle's cosets. See
    /// [`ExtCoeffConversion`].
    type ExtCoeffConv: ExtCoeffConversion<F, E>;
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv;
}

/// The recommended `Backend<BabyBearField, BabyBearExt4>` for the current
/// build target: the NEON backend on aarch64, the generic work-stealing
/// backend elsewhere. Concrete-BabyBear call sites (family provers, tests)
/// should use this alias via `DefaultBabyBearBackend::default()`.
#[cfg(target_arch = "aarch64")]
pub type DefaultBabyBearBackend = BabyBearNeonWorkStealingBackend;
/// The recommended `Backend<BabyBearField, BabyBearExt4>` for the current
/// build target: the NEON backend on aarch64, the generic work-stealing
/// backend elsewhere.
#[cfg(not(target_arch = "aarch64"))]
pub type DefaultBabyBearBackend = WorkStealingBackend;

/// Coset offsets `root^0..root^{lde_factor-1}` for message length `n`.
fn coset_offsets<F: PrimeField + TwoAdicField>(n: usize, lde_factor: usize) -> Vec<F> {
    let next_root = fft::domain_generator_for_size::<F>((n * lde_factor) as u64);
    fft::materialize_powers_serial_starting_with_one::<F, Global>(next_root, lde_factor)
}

/// How a batch's poly×coset FFT grid is executed. Chosen by [`plan_coset_grid`]
/// from the element width and the tasks/threads ratio. Applies only to the
/// purely in-memory prover paths this backend serves — the coset-by-coset
/// RECOMPUTE paths (local-testing storage policies) do not route through the
/// backend and are deliberately left un-optimized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CosetGridPlan {
    /// One SERIAL fused coset FFT per grid task, work-stolen across the pool.
    /// The default whenever tasks ≥ threads, and always for narrow (≤8 B)
    /// fields: splitting a single BabyBear-width FFT is nearly worthless
    /// (measured 2 threads ≈ 1.08× serial at 2^24 — the flat parallel butterfly
    /// loop overhead eats the gain), so leftover threads are better left to
    /// finish the tail early than spent inside FFTs.
    FlatSerialTasks,
    /// Fewer tasks than threads AND a wide (≥16 B) element type, whose per-FFT
    /// parallelism is worth it (measured ~90+% efficient on Proth120): grid
    /// tasks still run on the pool, but each task uses the worker-parallel
    /// pipeline; the nested scopes land on the SAME pool, so otherwise-idle
    /// threads steal butterfly chunks — effectively >1 thread per FFT without
    /// ever leaving the worker's thread budget.
    ParallelWithinTask,
}

/// Element width at which splitting one FFT across threads pays off (Proth120
/// and the 4×u32 extensions qualify; 4 B base fields do not).
const WIDE_ELEMENT_BYTES: usize = 16;

fn plan_coset_grid<El>(num_tasks: usize, worker: &Worker) -> CosetGridPlan {
    if core::mem::size_of::<El>() >= WIDE_ELEMENT_BYTES && num_tasks < worker.get_num_cores() {
        CosetGridPlan::ParallelWithinTask
    } else {
        CosetGridPlan::FlatSerialTasks
    }
}

/// One coset FFT executed according to `plan`: `serial_kernel` (the backend's
/// fused serial pipeline) for flat grid tasks, or `parallel_kernel` (the
/// backend's worker-wide pipeline, composing with an enclosing rayon task
/// through the shared pool). All kernels produce identical values; they are
/// the ONLY point where backends differ.
fn lde_coset_by_plan<F: Field, E: Field + FieldExtension<F>>(
    monomials: &[E],
    offset: F,
    twiddles_bit_reversed: &[F],
    plan: CosetGridPlan,
    serial_kernel: &(impl Fn(&[E], F, &[F]) -> Vec<E> + Sync),
    parallel_kernel: &(impl Fn(&[E], F, &[F], &Worker) -> Vec<E> + Sync),
    worker: &Worker,
) -> Vec<E> {
    match plan {
        CosetGridPlan::FlatSerialTasks => serial_kernel(monomials, offset, twiddles_bit_reversed),
        CosetGridPlan::ParallelWithinTask => {
            parallel_kernel(monomials, offset, twiddles_bit_reversed, worker)
        }
    }
}

/// The canonical worker-parallel coset pipeline (scale, bit-reverse, radix-2
/// NTT — each pass worker-wide): the `parallel_kernel` of the generic
/// [`WorkStealingBackend`].
fn lde_coset_canonical_parallel<F: Field, E: Field + FieldExtension<F>>(
    monomials: &[E],
    offset: F,
    twiddles_bit_reversed: &[F],
    worker: &Worker,
) -> Vec<E> {
    let n = monomials.len();
    let log_n = n.trailing_zeros();
    let mut evals = monomials.to_vec();
    if offset != F::ONE {
        fft::distribute_powers_parallel(&mut evals, F::ONE, offset, worker);
    }
    fft::parallel_bitreverse_enumeration_inplace(&mut evals, worker);
    fft::naive::parallel_ct_ntt_bitreversed_to_natural(
        &mut evals,
        log_n,
        &twiddles_bit_reversed[..(n / 2).max(1)],
        worker,
    );
    evals
}

/// Grid body of [`Backend::lde_multiple_polys_from_hypercubes`] for the
/// work-stealing backends, parameterized by the serial coset kernel.
fn ws_lde_multiple_polys_from_hypercubes<F: PrimeField + TwoAdicField>(
    evals: &[&[F]],
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    serial_kernel: &(impl Fn(&[F], F, &[F]) -> Vec<F> + Sync),
    to_monomial: &(impl Fn(&mut [F], u32) + Sync),
    parallel_kernel: &(impl Fn(&[F], F, &[F], &Worker) -> Vec<F> + Sync),
    worker: &Worker,
) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>> {
    use worker::rayon::prelude::*;

    {
        if evals.is_empty() {
            return (0..lde_factor).map(|_| Vec::new()).collect();
        }
        let n = evals[0].len();
        let num_cols = evals.len();
        let root_powers = coset_offsets::<F>(n, lde_factor);
        let tw = &twiddles.forward_twiddles[..];

        // 1. hypercube evals -> multilinear monomial coefficients. Planner: one
        //    serial transform per column (work-stolen) by default; only when the
        //    columns are MUCH fewer than the threads (below, factor 8) run them
        //    one after another with EACH transform worker-parallel. The factor
        //    matters: a parallel transform of a narrow-field column has barriers
        //    and a limited effective speedup, so `cols` sequential parallel
        //    transforms beat `cols` concurrent serial ones only when the spare
        //    parallelism per column is large (measured on 88-core SPR: 32 cols
        //    of 2^24 BabyBear ran 1.5x SLOWER sequential-parallel than
        //    par-over-cols with 56 threads idle).
        const PHASE1_PARALLEL_PER_COLUMN_FACTOR: usize = 8;
        let monomials: Vec<Vec<F>> = if num_cols * PHASE1_PARALLEL_PER_COLUMN_FACTOR
            > worker.get_num_cores()
        {
            worker.pool.install(|| {
                evals
                    .par_iter()
                    .map(|col| {
                        let mut v = col.to_vec();
                        let size_log2 = v.len().trailing_zeros();
                        fft::bitreverse_enumeration_inplace(&mut v);
                        to_monomial(&mut v, size_log2);
                        v
                    })
                    .collect()
            })
        } else {
            evals
                .iter()
                .map(|col| {
                    let mut v = col.to_vec();
                    let size_log2 = v.len().trailing_zeros();
                    fft::parallel_bitreverse_enumeration_inplace(&mut v, worker);
                    crate::gkr::whir::hypercube_to_monomial::parallel_multivariate_hypercube_evals_into_coeffs(
                        &mut v, size_log2, worker,
                    );
                    v
                })
                .collect()
        };

        // 2. (coset × column) FFT grid, execution mode from the planner (element
        //    width + tasks/threads ratio).
        let plan = plan_coset_grid::<F>(lde_factor * num_cols, worker);
        let flat: Vec<ColumnMajorCosetBoundTracePart<F, F>> = worker.pool.install(|| {
            (0..lde_factor * num_cols)
                .into_par_iter()
                .map(|t| {
                    let coset = t / num_cols;
                    let col = t % num_cols;
                    let offset = root_powers[coset];
                    let data = lde_coset_by_plan(
                        &monomials[col],
                        offset,
                        tw,
                        plan,
                        serial_kernel,
                        parallel_kernel,
                        worker,
                    );
                    ColumnMajorCosetBoundTracePart {
                        column: Arc::new(data.into_boxed_slice()),
                        offset,
                    }
                })
                .collect()
        });

        // reshape flat (coset-major) into [coset][column]
        let mut flat = flat.into_iter();
        (0..lde_factor)
            .map(|_| (0..num_cols).map(|_| flat.next().unwrap()).collect())
            .collect()
    }
}

/// Grid body of [`Backend::lde_packed_monomials_into_cosets`] for the
/// work-stealing backends, parameterized by the serial coset kernel.
fn ws_lde_packed_monomials_into_cosets<F: PrimeField + TwoAdicField>(
    monomials: Vec<Vec<F>>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    serial_kernel: &(impl Fn(&[F], F, &[F]) -> Vec<F> + Sync),
    parallel_kernel: &(impl Fn(&[F], F, &[F], &Worker) -> Vec<F> + Sync),
    worker: &Worker,
) -> Vec<ColumnMajorBaseOracleForCoset<F>> {
    use worker::rayon::prelude::*;

    {
        assert!(!monomials.is_empty());
        let n = monomials[0].len();
        let coset_size_log2 = n.trailing_zeros() as usize;
        for m in monomials.iter() {
            assert_eq!(m.len(), n);
        }
        let num_cols = monomials.len();
        let root_powers = coset_offsets::<F>(n, lde_factor);
        let tw = &twiddles.forward_twiddles[..];

        let plan = plan_coset_grid::<F>(lde_factor * num_cols, worker);
        let flat: Vec<ColumnMajorCosetBoundTracePart<F, F>> = worker.pool.install(|| {
            (0..lde_factor * num_cols)
                .into_par_iter()
                .map(|t| {
                    let coset = t / num_cols;
                    let col = t % num_cols;
                    let offset = root_powers[coset];
                    let data = lde_coset_by_plan(
                        &monomials[col],
                        offset,
                        tw,
                        plan,
                        serial_kernel,
                        parallel_kernel,
                        worker,
                    );
                    ColumnMajorCosetBoundTracePart {
                        column: Arc::new(data.into_boxed_slice()),
                        offset,
                    }
                })
                .collect()
        });

        let mut flat = flat.into_iter();
        (0..lde_factor)
            .map(|coset| ColumnMajorBaseOracleForCoset {
                original_values_normal_order: (0..num_cols).map(|_| flat.next().unwrap()).collect(),
                offset: root_powers[coset],
                coset_size_log2,
            })
            .collect()
    }
}

/// Grid body of the single-poly LDE methods (base- and extension-field twins)
/// for the work-stealing backends, parameterized by the serial coset kernel.
fn ws_lde_single_poly_from_monomial_form<F, El>(
    monomial_form_normal_order: &[El],
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    serial_kernel: &(impl Fn(&[El], F, &[F]) -> Vec<El> + Sync),
    parallel_kernel: &(impl Fn(&[El], F, &[F], &Worker) -> Vec<El> + Sync),
    worker: &Worker,
) -> Vec<(Box<[El]>, F)>
where
    F: PrimeField + TwoAdicField,
    El: FieldExtension<F> + Field,
{
    use worker::rayon::prelude::*;

    let n = monomial_form_normal_order.len();
    let root_powers = coset_offsets::<F>(n, lde_factor);
    let tw = &twiddles.forward_twiddles[..];

    let plan = plan_coset_grid::<El>(lde_factor, worker);
    worker.pool.install(|| {
        (0..lde_factor)
            .into_par_iter()
            .map(|coset| {
                let offset = root_powers[coset];
                let data = lde_coset_by_plan(
                    monomial_form_normal_order,
                    offset,
                    tw,
                    plan,
                    serial_kernel,
                    parallel_kernel,
                    worker,
                );
                (data.into_boxed_slice(), offset)
            })
            .collect()
    })
}

fn make_pows_local<T: Field>(el: T, num_powers: usize) -> Vec<T> {
    let mut result = Vec::with_capacity(num_powers);
    let mut current = el;
    for _ in 0..num_powers {
        result.push(current);
        current.square();
    }
    result
}

/// All-threads eq-poly contribution accumulation for the work-stealing
/// backends: each sample's full `2^log_n` equality table factors EXACTLY into
/// `hi (x) lo` tensors over the bit split (field multiplication is exact, so
/// the regrouped product is byte-identical to the reference's flat chain), so
/// instead of materializing `~64` full-size tables and accumulating them
/// SERIALLY (the reference), we build tiny per-sample tensors and make ONE
/// worker-parallel pass over the eq poly, accumulating all samples per element
/// in the reference's sample order.
fn ws_update_eq_poly<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    eq_poly: &mut [E],
    ood_samples: &[(E, E)],
    in_domain_samples: &[(F, E)],
    worker: &Worker,
) {
    let n = eq_poly.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros() as usize;
    if log_n < 2 {
        return crate::gkr::whir::update_eq_poly_reference(
            eq_poly,
            ood_samples,
            in_domain_samples,
            worker,
        );
    }
    // lo covers the LOW `log_c` index bits (the LAST log_c entries of the
    // squared-powers vector), hi the rest.
    let log_c = core::cmp::min(10, log_n - 1).max(1);
    let c = 1usize << log_c;
    let num_hi = n >> log_c;

    fn split_tensors<T: Field>(
        point: T,
        log_n: usize,
        log_c: usize,
        worker: &Worker,
    ) -> (Box<[T]>, Box<[T]>) {
        let pows = make_pows_local(point, log_n);
        let lo = crate::gkr::sumcheck::eq_poly::make_eq_poly_in_full::<T>(
            &pows[log_n - log_c..],
            worker,
        )
        .pop()
        .unwrap();
        let hi = if log_c == log_n {
            vec![T::ONE].into_boxed_slice()
        } else {
            crate::gkr::sumcheck::eq_poly::make_eq_poly_in_full::<T>(&pows[..log_n - log_c], worker)
                .pop()
                .unwrap()
        };
        (hi, lo)
    }

    #[expect(
        clippy::type_complexity,
        reason = "generic over field + allocator; a bound-free type alias would drop those bounds"
    )]
    let ood: Vec<(E, Box<[E]>, Box<[E]>)> = ood_samples
        .iter()
        .map(|(point, ch)| {
            let (hi, lo) = split_tensors(*point, log_n, log_c, worker);
            (*ch, hi, lo)
        })
        .collect();
    #[expect(
        clippy::type_complexity,
        reason = "generic over field + allocator; a bound-free type alias would drop those bounds"
    )]
    let base: Vec<(E, Box<[F]>, Box<[F]>)> = in_domain_samples
        .iter()
        .map(|(point, ch)| {
            let (hi, lo) = split_tensors(*point, log_n, log_c, worker);
            (*ch, hi, lo)
        })
        .collect();

    let base_addr = eq_poly.as_mut_ptr() as usize;
    let ood_ref = &ood;
    let base_ref = &base;
    worker.scope(num_hi, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(thread_idx);
            let size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut s_ood: Vec<E> = Vec::with_capacity(ood_ref.len());
                let mut s_base: Vec<E> = Vec::with_capacity(base_ref.len());
                for h in start..(start + size) {
                    s_ood.clear();
                    for (ch, hi, _) in ood_ref.iter() {
                        let mut s = *ch;
                        s.mul_assign(&hi[h]);
                        s_ood.push(s);
                    }
                    s_base.clear();
                    for (ch, hi, _) in base_ref.iter() {
                        let mut s = *ch;
                        s.mul_assign_by_base(&hi[h]);
                        s_base.push(s);
                    }
                    let dst = (base_addr as *mut E).wrapping_add(h << log_c);
                    for l in 0..c {
                        let mut acc = unsafe { *dst.wrapping_add(l) };
                        for (s, (_, _, lo)) in s_ood.iter().zip(ood_ref.iter()) {
                            let mut v = *s;
                            v.mul_assign(&lo[l]);
                            acc.add_assign(&v);
                        }
                        for (s, (_, _, lo)) in s_base.iter().zip(base_ref.iter()) {
                            let mut v = *s;
                            v.mul_assign_by_base(&lo[l]);
                            acc.add_assign(&v);
                        }
                        unsafe { *dst.wrapping_add(l) = acc };
                    }
                }
            });
        }
    });
}

/// All-threads `main domain -> monomial form` for the work-stealing backends:
/// worker-parallel inverse NTT, parallel `1/N` scaling, parallel bit-reversal.
/// Byte-identical to the serial reference.
fn ws_monomial_form_from_main_domain<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    source_domain: Vec<E>,
    twiddles: &Twiddles<F, Global>,
    worker: &Worker,
) -> Vec<E> {
    let n = source_domain.len();
    let log_n = n.trailing_zeros();
    let mut ifft = source_domain;
    let size_inv = F::from_u32_unchecked(n as u32).inverse().unwrap();
    fft::naive::parallel_ct_ntt_natural_to_bitreversed(
        &mut ifft,
        log_n,
        &twiddles.inverse_twiddles[..(n / 2).max(1)],
        worker,
    );
    worker.scope(n, |scope, geometry| {
        let mut rest = &mut ifft[..];
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let (chunk, tail) = rest.split_at_mut(chunk_size);
            rest = tail;
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for el in chunk.iter_mut() {
                    el.mul_assign_by_base(&size_inv);
                }
            });
        }
    });
    fft::parallel_bitreverse_enumeration_inplace(&mut ifft, worker);
    ifft
}

/// All-threads `monomial form -> hypercube evals` (+ bitrev) for the
/// work-stealing backends. Byte-identical to the serial reference.
fn ws_hypercube_evals_from_monomial_form<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
>(
    mut v: Vec<E>,
    worker: &Worker,
) -> Vec<E> {
    let log_n = v.len().trailing_zeros();
    crate::gkr::whir::hypercube_to_monomial::parallel_multivariate_coeffs_into_hypercube_evals(
        &mut v, log_n, worker,
    );
    fft::parallel_bitreverse_enumeration_inplace(&mut v, worker);
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use ::field::{Proth120, Rand};

    fn rand_cols<F: Rand>(num: usize, n: usize) -> Vec<Vec<F>> {
        let mut rng = rand::rng();
        (0..num)
            .map(|_| (0..n).map(|_| F::random_element(&mut rng)).collect())
            .collect()
    }

    fn check_equal_cosets<F: PrimeField + TwoAdicField>(
        a: &[Vec<ColumnMajorCosetBoundTracePart<F, F>>],
        b: &[Vec<ColumnMajorCosetBoundTracePart<F, F>>],
    ) {
        assert_eq!(a.len(), b.len());
        for (coset_a, coset_b) in a.iter().zip(b.iter()) {
            assert_eq!(coset_a.len(), coset_b.len());
            for (ca, cb) in coset_a.iter().zip(coset_b.iter()) {
                assert_eq!(ca.offset, cb.offset);
                assert_eq!(&ca.column[..], &cb.column[..]);
            }
        }
    }

    /// The work-stealing backend must produce exactly the same values as the
    /// naive one for every method (proofs must not depend on the backend).
    /// Exercised in BOTH planner regimes: `num_cols`/`lde` combinations with
    /// tasks ≥ threads (flat serial grid) and with tasks < threads (parallel
    /// within task for wide fields, parallel phase-1 transforms).
    fn check_backend_parity_shape<F: PrimeField + TwoAdicField + Rand>(
        num_threads: usize,
        num_cols: usize,
        n_log: usize,
        lde: usize,
    ) {
        let worker = Worker::new_with_num_threads(num_threads);
        let n = 1usize << n_log;
        let twiddles = Twiddles::<F, Global>::new(n, &worker);
        let cols: Vec<Vec<F>> = rand_cols(num_cols, n);
        let col_refs: Vec<&[F]> = cols.iter().map(|c| &c[..]).collect();

        let a = Backend::<F, F>::lde_multiple_polys_from_hypercubes(
            &NaiveBackend,
            &col_refs,
            &twiddles,
            lde,
            &worker,
        );
        let b = Backend::<F, F>::lde_multiple_polys_from_hypercubes(
            &WorkStealingBackend,
            &col_refs,
            &twiddles,
            lde,
            &worker,
        );
        check_equal_cosets(&a, &b);

        // packed-monomials variant (inputs already in monomial form)
        let monomials: Vec<Vec<F>> = rand_cols(num_cols, n);
        let a = Backend::<F, F>::lde_packed_monomials_into_cosets(
            &NaiveBackend,
            monomials.clone(),
            &twiddles,
            lde,
            &worker,
        );
        let b = Backend::<F, F>::lde_packed_monomials_into_cosets(
            &WorkStealingBackend,
            monomials,
            &twiddles,
            lde,
            &worker,
        );
        assert_eq!(a.len(), b.len());
        for (ca, cb) in a.iter().zip(b.iter()) {
            assert_eq!(ca.offset, cb.offset);
            assert_eq!(ca.coset_size_log2, cb.coset_size_log2);
            assert_eq!(
                ca.original_values_normal_order.len(),
                cb.original_values_normal_order.len()
            );
            for (x, y) in ca
                .original_values_normal_order
                .iter()
                .zip(cb.original_values_normal_order.iter())
            {
                assert_eq!(x.offset, y.offset);
                assert_eq!(&x.column[..], &y.column[..]);
            }
        }
    }

    fn check_backend_parity<F: PrimeField + TwoAdicField + Rand>() {
        // tasks >= threads: flat serial grid, par-over-cols transforms
        check_backend_parity_shape::<F>(4, 5, 10, 8);
        // tasks < threads: wide fields take the parallel-within-task branch,
        // and (cols*8 <= threads) the phase-1 transforms run worker-parallel
        check_backend_parity_shape::<F>(8, 1, 10, 2);
    }

    fn check_ext_parity_shape<
        F: PrimeField + TwoAdicField + Rand,
        E: FieldExtension<F> + Field + Rand,
    >(
        num_threads: usize,
        lde: usize,
    ) {
        let worker = Worker::new_with_num_threads(num_threads);
        let n = 1usize << 9;
        let twiddles = Twiddles::<F, Global>::new(n, &worker);
        let mono: Vec<E> = rand_cols::<E>(1, n).pop().unwrap();

        let a = Backend::<F, E>::lde_ext_poly_from_monomial_form(
            &NaiveBackend,
            &mono,
            &twiddles,
            lde,
            &worker,
        );
        let b = Backend::<F, E>::lde_ext_poly_from_monomial_form(
            &WorkStealingBackend,
            &mono,
            &twiddles,
            lde,
            &worker,
        );
        assert_eq!(a.len(), b.len());
        for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
            assert_eq!(oa, ob);
            assert_eq!(&da[..], &db[..]);
        }
    }

    fn check_ext_parity<
        F: PrimeField + TwoAdicField + Rand,
        E: FieldExtension<F> + Field + Rand,
    >() {
        // tasks >= threads (flat serial grid)
        check_ext_parity_shape::<F, E>(4, 16);
        // tasks < threads (parallel-within-task for wide E)
        check_ext_parity_shape::<F, E>(8, 2);
    }

    /// The two O(1) batched-poly transforms must match NaiveBackend exactly
    /// for any backend `b`, across sizes covering the parallel thresholds and
    /// stage-count parities.
    fn check_o1_transform_parity<
        F: PrimeField + TwoAdicField + Rand,
        E: FieldExtension<F> + Field + Rand,
        B: Backend<F, E>,
    >(
        b: &B,
    ) {
        let worker = Worker::new_with_num_threads(4);

        // eq-poly contribution accumulation: the tensor-split batched version
        // must equal the reference exactly (1 OOD + many base samples, sizes
        // around the chunk split incl. log_n <= log_c edge)
        {
            let mut rng = rand::rng();
            for n_log in [1u32, 3, 9, 11, 13] {
                let n = 1usize << n_log;
                let mut a: Vec<E> = rand_cols::<E>(1, n).pop().unwrap();
                let mut b_poly = a.clone();
                let ood: Vec<(E, E)> =
                    vec![(E::random_element(&mut rng), E::random_element(&mut rng))];
                let base: Vec<(F, E)> = (0..13)
                    .map(|_| (F::random_element(&mut rng), E::random_element(&mut rng)))
                    .collect();
                Backend::<F, E>::update_eq_poly(&NaiveBackend, &mut a, &ood, &base, &worker);
                b.update_eq_poly(&mut b_poly, &ood, &base, &worker);
                assert_eq!(a, b_poly, "update_eq_poly diverged at n_log={n_log}");
            }
        }
        for n_log in [3u32, 8, 13, 14] {
            let n = 1usize << n_log;
            let twiddles = Twiddles::<F, Global>::new(n, &worker);
            let v: Vec<E> = rand_cols::<E>(1, n).pop().unwrap();

            let a = Backend::<F, E>::monomial_form_from_main_domain(
                &NaiveBackend,
                v.clone(),
                &twiddles,
                &worker,
            );
            let bres = b.monomial_form_from_main_domain(v.clone(), &twiddles, &worker);
            assert_eq!(a, bres, "monomial_form diverged at n_log={n_log}");

            let a = Backend::<F, E>::hypercube_evals_from_monomial_form(
                &NaiveBackend,
                v.clone(),
                &worker,
            );
            let bres = b.hypercube_evals_from_monomial_form(v, &worker);
            assert_eq!(a, bres, "hypercube_evals diverged at n_log={n_log}");
        }
    }

    #[test]
    fn work_stealing_backend_matches_naive_babybear() {
        check_backend_parity::<BabyBearField>();
        check_ext_parity::<BabyBearField, BabyBearExt4>();
        check_o1_transform_parity::<BabyBearField, BabyBearExt4, _>(&WorkStealingBackend);
    }

    #[test]
    fn work_stealing_backend_matches_naive_proth120() {
        check_backend_parity::<Proth120>();
        check_ext_parity::<Proth120, Proth120>();
        check_o1_transform_parity::<Proth120, Proth120, _>(&Proth120WorkStealingLazyBackend);
    }

    /// The LAZY backend (Proth120-only by construction — it does not implement
    /// `Backend` for any other field) must match NaiveBackend exactly on every
    /// LDE method, exercising the lazy-reduction serial kernel.
    /// The NEON BabyBear backend (aarch64-only, `Backend<BabyBear, Ext4>` by
    /// construction) must match NaiveBackend exactly on every method,
    /// including TINY polys (n < 16 degrades to the scalar reference) and the
    /// parallel-within-task plan.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn baby_bear_neon_backend_matches_naive() {
        type F = BabyBearField;
        let backend = BabyBearNeonWorkStealingBackend;

        // n covers: fallback (8 < 16), NEON without radix-4 pass (16), NEON
        // with radix-4 + u64-acc passes (1024/4096)
        for (num_threads, num_cols, n_log, lde) in
            [(4, 5, 3, 2), (4, 3, 4, 2), (4, 5, 10, 8), (8, 2, 12, 2)]
        {
            let worker = Worker::new_with_num_threads(num_threads);
            let n = 1usize << n_log;
            let twiddles = Twiddles::<F, Global>::new(n, &worker);
            let cols: Vec<Vec<F>> = rand_cols(num_cols, n);
            let col_refs: Vec<&[F]> = cols.iter().map(|c| &c[..]).collect();

            let a = Backend::<F, BabyBearExt4>::lde_multiple_polys_from_hypercubes(
                &NaiveBackend,
                &col_refs,
                &twiddles,
                lde,
                &worker,
            );
            let b = backend.lde_multiple_polys_from_hypercubes(&col_refs, &twiddles, lde, &worker);
            check_equal_cosets(&a, &b);

            let mono: Vec<F> = rand_cols::<F>(1, n).pop().unwrap();
            let a = Backend::<F, BabyBearExt4>::lde_base_poly_from_monomial_form(
                &NaiveBackend,
                &mono,
                &twiddles,
                lde,
                &worker,
            );
            let b = backend.lde_base_poly_from_monomial_form(&mono, &twiddles, lde, &worker);
            assert_eq!(a.len(), b.len());
            for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
                assert_eq!(oa, ob);
                assert_eq!(&da[..], &db[..]);
            }

            let mono_ext: Vec<BabyBearExt4> = rand_cols::<BabyBearExt4>(1, n).pop().unwrap();
            let a = Backend::<F, BabyBearExt4>::lde_ext_poly_from_monomial_form(
                &NaiveBackend,
                &mono_ext,
                &twiddles,
                lde,
                &worker,
            );
            let b = backend.lde_ext_poly_from_monomial_form(&mono_ext, &twiddles, lde, &worker);
            assert_eq!(a.len(), b.len());
            for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
                assert_eq!(oa, ob);
                assert_eq!(&da[..], &db[..]);
            }
        }
        check_o1_transform_parity::<BabyBearField, BabyBearExt4, _>(&backend);
    }

    /// The NEON leaf-fold conversion must be byte-identical to the scalar
    /// context, across the production leaf widths (8/16/32), both scheduling
    /// entry points, and a non-trivial coset offset.
    #[cfg(all(target_arch = "aarch64", not(feature = "eval_leaves")))]
    #[test]
    fn baby_bear_neon_ext_coeff_conv_matches_scalar() {
        use crate::gkr::whir::ExtCoeffConvCtx;
        let worker = Worker::new_with_num_threads(4);
        let mut rng = rand::rng();
        for (coset_log, vpl) in [(10usize, 8usize), (12, 16), (12, 32), (8, 2), (6, 64)] {
            let n = 1usize << coset_log;
            let column: Vec<BabyBearExt4> = (0..n)
                .map(|_| BabyBearExt4::random_element(&mut rng))
                .collect();
            let offset = fft::domain_generator_for_size::<BabyBearField>((n * 2) as u64);

            let ctx = ExtCoeffConvCtx::<BabyBearField>::new(n, vpl);
            let mut expected = column.clone();
            ctx.apply(&mut expected, offset, &worker);

            let conv = super::aarch64::BabyBearNeonExtCoeffConv::new(n, vpl);
            let mut got = column.clone();
            ExtCoeffConversion::<BabyBearField, BabyBearExt4>::apply(
                &conv, &mut got, offset, &worker,
            );
            assert_eq!(
                got, expected,
                "NEON conv (parallel) diverged at 2^{coset_log} vpl {vpl}"
            );

            let mut got = column.clone();
            ExtCoeffConversion::<BabyBearField, BabyBearExt4>::apply_serial(
                &conv, &mut got, offset,
            );
            assert_eq!(
                got, expected,
                "NEON conv (serial) diverged at 2^{coset_log} vpl {vpl}"
            );
        }
    }

    #[test]
    fn work_stealing_lazy_backend_matches_naive_proth120() {
        type F = Proth120;
        let worker = Worker::new_with_num_threads(4);
        let n = 1usize << 10;
        let lde = 8usize;
        let twiddles = Twiddles::<F, Global>::new(n, &worker);
        let cols: Vec<Vec<F>> = rand_cols(5, n);
        let col_refs: Vec<&[F]> = cols.iter().map(|c| &c[..]).collect();

        let a = Backend::<F, F>::lde_multiple_polys_from_hypercubes(
            &NaiveBackend,
            &col_refs,
            &twiddles,
            lde,
            &worker,
        );
        let b = Proth120WorkStealingLazyBackend
            .lde_multiple_polys_from_hypercubes(&col_refs, &twiddles, lde, &worker);
        check_equal_cosets(&a, &b);

        let mono: Vec<F> = rand_cols::<F>(1, n).pop().unwrap();
        let a = Backend::<F, F>::lde_base_poly_from_monomial_form(
            &NaiveBackend,
            &mono,
            &twiddles,
            lde,
            &worker,
        );
        let b = Proth120WorkStealingLazyBackend
            .lde_base_poly_from_monomial_form(&mono, &twiddles, lde, &worker);
        assert_eq!(a.len(), b.len());
        for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
            assert_eq!(oa, ob);
            assert_eq!(&da[..], &db[..]);
        }

        let c = Proth120WorkStealingLazyBackend
            .lde_ext_poly_from_monomial_form(&mono, &twiddles, lde, &worker);
        assert_eq!(a.len(), c.len());
        for ((da, oa), (dc, oc)) in a.iter().zip(c.iter()) {
            assert_eq!(oa, oc);
            assert_eq!(&da[..], &dc[..]);
        }

        // tasks < threads: the PARALLEL-within-task plan (the intermediate-
        // WHIR-oracle shape) must route through the worker-parallel lazy
        // radix-8 pipeline and still match exactly. n above the parallel
        // pipeline's serial-fallback threshold (2^13).
        let worker = Worker::new_with_num_threads(8);
        let n = 1usize << 14;
        let lde = 2usize;
        let twiddles = Twiddles::<F, Global>::new(n, &worker);
        let mono: Vec<F> = rand_cols::<F>(1, n).pop().unwrap();
        let a = Backend::<F, F>::lde_ext_poly_from_monomial_form(
            &NaiveBackend,
            &mono,
            &twiddles,
            lde,
            &worker,
        );
        let b = Proth120WorkStealingLazyBackend
            .lde_ext_poly_from_monomial_form(&mono, &twiddles, lde, &worker);
        assert_eq!(a.len(), b.len());
        for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
            assert_eq!(oa, ob);
            assert_eq!(&da[..], &db[..]);
        }
    }
}
