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
use fft::{GoodAllocator, Twiddles};
use field::{Field, FieldExtension, PrimeField, Proth120, TwoAdicField};
use std::alloc::Global;
use std::sync::Arc;
use worker::Worker;

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
pub trait Backend<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>:
    Send + Sync
{
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
    /// batched proximity polynomial in `whir_fold`. Mirrors
    /// `compute_column_major_monomial_form_from_main_domain_owned`.
    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<E>,
        twiddles: &Twiddles<F, Global>,
        worker: &Worker,
    ) -> Vec<E>;
}

/// Work-stealing implementation: identical values to [`NaiveBackend`], but the
/// LDE work is flattened into a `poly × coset` task grid and distributed over
/// the [`Worker`]'s rayon thread pool, with each task running the fused SERIAL
/// coset pipeline (`fft::lde_coset_natural_seq_fused`).
///
/// Why: the naive scheduling parallelizes either over polynomials only (base
/// commits — idle cores when few columns meet many cores) or runs cosets
/// sequentially with one barrier-heavy parallel NTT per coset (packed commits —
/// per-FFT parallel efficiency measured at only ~30–50% beyond 8 threads,
/// because every NTT stage is a synchronization barrier). Independent serial
/// FFTs have no barriers at all: with `polys × lde_factor` tasks (e.g. 7 packed
/// polys × 32 cosets = 224 tasks for the unified Proth120 circuit) every core
/// stays busy until the tail, and rayon's work stealing absorbs the imbalance.
#[derive(Clone, Copy, Debug, Default)]
pub struct WorkStealingBackend;

/// Work-stealing backend running Proth120 LAZY-REDUCTION RADIX-8 coset
/// kernels on BOTH planner branches: values held in `[0, 2p)` through the NTT
/// (the Montgomery multiply loses its final conditional subtraction; one
/// canonicalization pass at the end), and three butterfly levels fused per
/// sweep (radix-4 / fused-radix-2 passes absorb leftover levels) — the array
/// is traversed ~log_n/3 times instead of log_n, which matters most when the
/// work saturates DRAM bandwidth (measured 2.0x vs the canonical kernel at
/// 224 concurrent 2^26 tasks on 88-core Sapphire Rapids; ~1.6x serial).
///
/// - Flat grid tasks (tasks ≥ threads — the base commits) run the SERIAL
///   `fft::proth120_lazy::lde_coset_lazy_r8`.
/// - The parallel-within-task plan (tasks < threads — notably the SMALLER
///   intermediate-WHIR-oracle FFTs, where `lde_factor` cosets < cores) runs
///   the worker-parallel `fft::proth120_lazy::lde_coset_lazy_parallel_r8`, so
///   the shrinking fold sizes keep the radix + lazy benefits.
///
/// Outputs are bit-identical to [`WorkStealingBackend`] / [`NaiveBackend`].
/// Implemented ONLY for `Backend<Proth120, Proth120>` — the kernels are
/// field-specific, and callers opt in where they concretely know the field
/// (the Proth120 tests/examples) instead of any runtime type dispatch.
#[derive(Clone, Copy, Debug, Default)]
pub struct Proth120WorkStealingLazyBackend;

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
        CosetGridPlan::FlatSerialTasks => {
            serial_kernel(monomials, offset, twiddles_bit_reversed)
        }
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
                        crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs(
                            &mut v, size_log2,
                        );
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
                    let data =
                        lde_coset_by_plan(&monomials[col], offset, tw, plan, serial_kernel, parallel_kernel, worker);
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
                    let data =
                        lde_coset_by_plan(&monomials[col], offset, tw, plan, serial_kernel, parallel_kernel, worker);
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

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> Backend<F, E>
    for WorkStealingBackend
{
    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[F]],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>> {
        ws_lde_multiple_polys_from_hypercubes(
            evals,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<F>>,
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<F>> {
        ws_lde_packed_monomials_into_cosets(
            monomials,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[E],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[E]>, F)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[F],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[F]>, F)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[F]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<F>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<E>,
        twiddles: &Twiddles<F, Global>,
        _worker: &Worker,
    ) -> Vec<E> {
        compute_column_major_monomial_form_from_main_domain_owned::<F, E, Global>(
            source_domain,
            twiddles,
        )
    }
}

impl Backend<Proth120, Proth120> for Proth120WorkStealingLazyBackend {
    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[Proth120]],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<Proth120, Proth120>>> {
        ws_lde_multiple_polys_from_hypercubes(
            evals,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<Proth120>>,
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<Proth120>> {
        ws_lde_packed_monomials_into_cosets(
            monomials,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[Proth120],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[Proth120]>, Proth120)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[Proth120],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[Proth120]>, Proth120)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[Proth120]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<Proth120>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<Proth120>,
        twiddles: &Twiddles<Proth120, Global>,
        _worker: &Worker,
    ) -> Vec<Proth120> {
        compute_column_major_monomial_form_from_main_domain_owned::<Proth120, Proth120, Global>(
            source_domain,
            twiddles,
        )
    }
}

/// The reference implementation: delegates verbatim to the historical free
/// functions, for any `<F, E>`.
#[derive(Clone, Copy, Debug, Default)]
pub struct NaiveBackend;

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> Backend<F, E> for NaiveBackend {
    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[F]],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>> {
        lde_multiple_polys_parallel_from_hypercubes(evals, twiddles, lde_factor, worker)
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<F>>,
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<F>> {
        lde_packed_monomials_into_cosets(monomials, twiddles, lde_factor, worker)
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[E],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[E]>, F)> {
        compute_column_major_lde_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            Some(worker),
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[F],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[F]>, F)> {
        compute_column_major_lde_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            Some(worker),
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[F]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<F>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<E>,
        twiddles: &Twiddles<F, Global>,
        _worker: &Worker,
    ) -> Vec<E> {
        compute_column_major_monomial_form_from_main_domain_owned::<F, E, Global>(
            source_domain,
            twiddles,
        )
    }
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

    #[test]
    fn work_stealing_backend_matches_naive_babybear() {
        check_backend_parity::<BabyBearField>();
        check_ext_parity::<BabyBearField, BabyBearExt4>();
    }

    #[test]
    fn work_stealing_backend_matches_naive_proth120() {
        check_backend_parity::<Proth120>();
        check_ext_parity::<Proth120, Proth120>();
    }

    /// The LAZY backend (Proth120-only by construction — it does not implement
    /// `Backend` for any other field) must match NaiveBackend exactly on every
    /// LDE method, exercising the lazy-reduction serial kernel.
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
        let b = Proth120WorkStealingLazyBackend.lde_multiple_polys_from_hypercubes(
            &col_refs, &twiddles, lde, &worker,
        );
        check_equal_cosets(&a, &b);

        let mono: Vec<F> = rand_cols::<F>(1, n).pop().unwrap();
        let a = Backend::<F, F>::lde_base_poly_from_monomial_form(
            &NaiveBackend,
            &mono,
            &twiddles,
            lde,
            &worker,
        );
        let b = Proth120WorkStealingLazyBackend.lde_base_poly_from_monomial_form(
            &mono, &twiddles, lde, &worker,
        );
        assert_eq!(a.len(), b.len());
        for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
            assert_eq!(oa, ob);
            assert_eq!(&da[..], &db[..]);
        }

        let c = Proth120WorkStealingLazyBackend.lde_ext_poly_from_monomial_form(
            &mono, &twiddles, lde, &worker,
        );
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
        let b = Proth120WorkStealingLazyBackend.lde_ext_poly_from_monomial_form(
            &mono, &twiddles, lde, &worker,
        );
        assert_eq!(a.len(), b.len());
        for ((da, oa), (db, ob)) in a.iter().zip(b.iter()) {
            assert_eq!(oa, ob);
            assert_eq!(&da[..], &db[..]);
        }
    }
}
