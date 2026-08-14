//! Production driver for the UNFUSED LSB uniskip chain over a same-size
//! layer: every pass emits one 16-point univariate covering 3 variables
//! (bound LSB-first, so all reads are groups of 8 consecutive elements),
//! then a separate streaming fold binds the drawn challenge's Lagrange
//! weights. Kernels are the `lsb_bench` set validated by the chain test.
//!
//! Architecture contract: this module COMPUTES only. The transcript
//! (commit/draw), claim chaining, and all self-checks live at the caller,
//! which supplies `on_round` -- called with each uniskip pass's 16
//! evaluations or each scalar tail round's (h0, hinf) pair, returning the
//! drawn folding challenge -- and the per-pass eq suffix tables plus the
//! tail suffix table (orientation conventions stay at the caller).

use std::collections::BTreeMap;

use super::full_size_scratch::produce_descriptions_from_batched_description;
#[cfg(target_arch = "aarch64")]
use super::lsb_bench;
use super::lsb_generic;
use super::program::build_soa_program;
use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelCollector;
use crate::gkr::sumcheck::access_and_fold::{DisjointAccessQuasiSlice, GKRStorage};
use crate::gkr::sumcheck::evaluation_kernels::BatchedGKRTermDescriptionConstants;
use crate::worker::Worker;
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};

/// One sumcheck round of the chain, as seen by the transcript driver.
pub(crate) enum ChainRound<E> {
    /// a width-3 uniskip pass: the 16 domain evaluations of q_g
    Pass { pass: usize, q16: [E; 16] },
    /// a scalar round (a window-pass round or a tail round) binding
    /// variable `round`: (h(0), leading coefficient) of the quadratic inner
    /// sum, before the eq(X, tau) factor
    Tail { round: usize, h0: E, hinf: E },
}

/// The engine's per-pass kind: a width-3 uniskip pass (one 16-point
/// univariate for 3 variables) or a width-3 window pass (a 27-cell
/// accumulator emitting 3 ordinary scalar rounds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChainPassKind {
    Uniskip3,
    Window3,
}

/// Per-platform kernel set for the chain's passes and folds: NEON for the
/// aarch64 BabyBear pair, the portable `lsb_generic` field-op kernels
/// otherwise. Selected once per layer; both produce identical values.
enum ChainKernels<F: PrimeField> {
    #[cfg(target_arch = "aarch64")]
    Neon(lsb_bench::LsbLdeAny),
    Generic(lsb_generic::Lde8Matrix<F>),
}

/// One uniskip pass's 16-point evaluation via the platform kernel set
/// (head pass reads the original sources, ext passes the folded slots).
#[allow(clippy::too_many_arguments)]
fn run_uniskip_pass_kernel<F: PrimeField, E: FieldExtension<F> + Field>(
    g: usize,
    kernels: &ChainKernels<F>,
    base_sources: &[DisjointAccessQuasiSlice<F, false>],
    ext_sources: &[DisjointAccessQuasiSlice<E, false>],
    srcs: &[DisjointAccessQuasiSlice<E, false>],
    prog: &super::program::OwnedSoaProgram<F, E>,
    eq_suffix: &[E],
    out_size: usize,
    worker: &Worker,
) -> [E; 16]
where
    [(); E::DEGREE]: Sized,
{
    if g == 0 {
        match kernels {
            #[cfg(target_arch = "aarch64")]
            ChainKernels::Neon(lde_tables) => {
                lsb_bench::lsb_soa_full_parallel::<F, E, 4, 4, 16, 2>(
                    base_sources,
                    ext_sources,
                    &prog.base_interp,
                    &prog.ext_interp,
                    Some(lde_tables),
                    &prog.forms,
                    &prog.products,
                    &prog.rest_steps,
                    &prog.additive_constant,
                    eq_suffix,
                    out_size,
                    worker,
                    lsb_bench::PH_ALL,
                )
            }
            ChainKernels::Generic(mat) => lsb_generic::head_pass::<F, E>(
                base_sources,
                ext_sources,
                prog,
                mat,
                eq_suffix,
                out_size,
                worker,
            ),
        }
    } else {
        match kernels {
            #[cfg(target_arch = "aarch64")]
            ChainKernels::Neon(lde_tables) => {
                if out_size % 2 == 0 {
                    lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 2>(
                        srcs,
                        &prog.forms,
                        &prog.products,
                        &prog.folded_quad,
                        &prog.folded_lin,
                        &prog.additive_constant,
                        lde_tables,
                        eq_suffix,
                        out_size,
                        worker,
                    )
                } else {
                    lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 1>(
                        srcs,
                        &prog.forms,
                        &prog.products,
                        &prog.folded_quad,
                        &prog.folded_lin,
                        &prog.additive_constant,
                        lde_tables,
                        eq_suffix,
                        out_size,
                        worker,
                    )
                }
            }
            ChainKernels::Generic(mat) => {
                lsb_generic::ext_pass::<F, E>(srcs, prog, mat, eq_suffix, out_size, worker)
            }
        }
    }
}

/// Runs the chain; `None` means the shape guard does not apply (caller falls
/// back). On success returns the per-input final evaluations
/// (each poly folded by all passes' challenge weights).
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_lsb_uniskip_chain<
    F: PrimeField + field::TwoAdicField,
    E: FieldExtension<F> + Field,
    OnRound: FnMut(ChainRound<E>) -> E,
>(
    collector: &KernelCollector<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    gkr_storage: &mut GKRStorage<F, E>,
    folding_steps: usize,
    pass_kinds: &[ChainPassKind],
    // for each Window3 pass: the prev point's scalar coordinates of the
    // window's SECOND and THIRD variables (the first enters via the round
    // callback); None for uniskip passes
    window_taus: &[Option<[E; 2]>],
    eq_suffixes: &[Box<[E]>],
    tail_t_table: &mut Vec<E>,
    fold_arena: &mut [Box<[core::mem::MaybeUninit<E>]>],
    worker: &Worker,
    mut on_round: OnRound,
) -> Option<BTreeMap<GKRAddress, E>>
where
    [(); E::DEGREE]: Sized,
{
    {
        if folding_steps < 6 {
            return None;
        }
        let omega16_f: F = ::fft::domain_generator_for_size::<F>(16);
        let num_passes = pass_kinds.len();
        assert!(3 * num_passes <= folding_steps);
        let tail_rounds = folding_steps - 3 * num_passes;
        assert_eq!(eq_suffixes.len(), num_passes);
        assert_eq!(window_taus.len(), num_passes);
        assert!(num_passes >= 1, "the chain schedule must open with a pass");
        // a uniskip pass consumes a RAW claim; scalar rounds leave an
        // eq-factored claim behind, so uniskip passes must come first
        let first_window = pass_kinds
            .iter()
            .position(|k| *k == ChainPassKind::Window3)
            .unwrap_or(num_passes);
        assert!(
            pass_kinds[first_window..]
                .iter()
                .all(|k| *k == ChainPassKind::Window3),
            "uniskip passes must precede window passes"
        );
        // the tail suffix table covers the variables ABOVE the first tail
        // round's variable; contracted by pair-sum after every tail round
        if tail_rounds > 0 {
            assert_eq!(tail_t_table.len(), 1usize << (tail_rounds - 1));
        }

        let description = collector.make_batched_description(challenge_constants, collector.layer);
        let (_compact, base_addrs, ext_addrs) =
            produce_descriptions_from_batched_description(&description);

        let mut base_sources = Vec::with_capacity(base_addrs.len());
        for addr in base_addrs.iter() {
            base_sources.push(DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                gkr_storage.try_get_base_poly(*addr)?,
            ));
        }
        let mut ext_sources = Vec::with_capacity(ext_addrs.len());
        for addr in ext_addrs.iter() {
            ext_sources.push(DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                gkr_storage.try_get_ext_poly(*addr)?,
            ));
        }

        let prog = build_soa_program(&description, collector, &base_addrs, &ext_addrs);

        // A/B knob: force the portable kernels on platforms where NEON
        // applies, for cross-validation of the two implementations
        let force_generic = std::env::var("GKR_FORCE_GENERIC_UNISKIP").is_ok();
        #[cfg(target_arch = "aarch64")]
        let kernels: ChainKernels<F> =
            if const { super::neon::is_bb_pair::<F, E>() } && !force_generic {
                let omega16_bb =
                    ::fft::domain_generator_for_size::<::field::baby_bear::base::BabyBearField>(16);
                let mut omega8_bb = omega16_bb;
                omega8_bb.square();
                ChainKernels::Neon(lsb_bench::LsbLdeAny::K8Mat(
                    super::neon::LsbLde8MatTables::new(omega8_bb, omega16_bb),
                ))
            } else {
                ChainKernels::Generic(lsb_generic::Lde8Matrix::new(omega16_f))
            };
        #[cfg(not(target_arch = "aarch64"))]
        let kernels: ChainKernels<F> = {
            let _ = force_generic; // no NEON alternative off-arm
            ChainKernels::Generic(lsb_generic::Lde8Matrix::new(omega16_f))
        };

        let nb = base_sources.len();
        let m = 1usize << folding_steps;
        // caller-provided fold arena, one buffer per input poly in
        // base-then-ext order; the chain's dense fold outputs live in
        // consecutive regions: one per pass (m/8, m/64, ...) plus -- for a
        // truncated schedule -- the tail's halving folds (< one live region)
        assert_eq!(fold_arena.len(), nb + ext_sources.len());
        let required_capacity = {
            let mut cap = 0usize;
            let mut live = m;
            for _ in 0..num_passes {
                live >>= 3;
                cap += live;
            }
            if tail_rounds > 0 {
                cap += live;
            }
            cap
        };
        for b in fold_arena.iter() {
            assert!(b.len() >= required_capacity);
        }
        let mut live_off = 0usize;
        let mut live_len = 0usize;
        let mut srcs: Vec<DisjointAccessQuasiSlice<E, false>> =
            Vec::with_capacity(fold_arena.len());

        for g in 0..num_passes {
            let out_size = 1usize << (folding_steps - 3 * g - 3);
            assert_eq!(eq_suffixes[g].len(), out_size.max(1));

            // sources view for ext passes (pass > 0): the previous pass's
            // dense fold output
            if g > 0 {
                srcs.clear();
                for buf in fold_arena.iter() {
                    let view = unsafe {
                        core::slice::from_raw_parts(
                            buf.as_ptr().add(live_off) as *const E,
                            live_len,
                        )
                    };
                    srcs.push(DisjointAccessQuasiSlice::<_, false>::from_init_slice(view));
                }
            }

            // per-pass fold weights over the 8 window values: Lagrange L(r)
            // for a uniskip pass, the eq tensor of the three drawn
            // challenges for a window pass
            let lw: [E; 8] = match pass_kinds[g] {
                ChainPassKind::Uniskip3 => {
                    let q = run_uniskip_pass_kernel::<F, E>(
                        g,
                        &kernels,
                        &base_sources,
                        &ext_sources,
                        &srcs,
                        &prog,
                        &eq_suffixes[g],
                        out_size,
                        worker,
                    );
                    // caller owns transcript + self-checks; hands back r
                    let r = on_round(ChainRound::Pass { pass: g, q16: q });
                    super::uniskip::uniskip8_fold_weights::<F, E>(&r, omega16_f)
                }
                ChainPassKind::Window3 => {
                    let acc27: [E; 27] = if g == 0 {
                        lsb_generic::window27_head_pass::<F, E>(
                            &base_sources,
                            &ext_sources,
                            &prog,
                            &eq_suffixes[g],
                            out_size,
                            worker,
                        )
                    } else {
                        lsb_generic::window27_ext_pass::<F, E>(
                            &srcs,
                            &prog,
                            &eq_suffixes[g],
                            out_size,
                            worker,
                        )
                    };
                    let [tau1, tau2] = window_taus[g].expect("window pass needs intra-window taus");
                    let eqf = |x: usize, t: &E| -> E {
                        if x == 0 {
                            let mut v = E::ONE;
                            v.sub_assign(t);
                            v
                        } else {
                            *t
                        }
                    };
                    let eq4: [E; 4] = core::array::from_fn(|i| {
                        // matrix contraction layout: eq4[2*x1 + x2]
                        let mut v = eqf(i >> 1, &tau1);
                        v.mul_assign(&eqf(i & 1, &tau2));
                        v
                    });
                    let eq2: [E; 2] = core::array::from_fn(|i| eqf(i, &tau2));

                    use super::{
                        bind_accumulator_27, bind_accumulator_9,
                        evaluate_claim_from_intermediate_matrix_27,
                        evaluate_claim_from_intermediate_matrix_9,
                    };
                    let e3 = evaluate_claim_from_intermediate_matrix_27(&eq4, &acc27);
                    let r0 = on_round(ChainRound::Tail {
                        round: 3 * g,
                        h0: e3[0],
                        hinf: e3[2],
                    });
                    let acc9 = bind_accumulator_27(&acc27, &r0);
                    let e3 = evaluate_claim_from_intermediate_matrix_9(&eq2, &acc9);
                    let r1 = on_round(ChainRound::Tail {
                        round: 3 * g + 1,
                        h0: e3[0],
                        hinf: e3[2],
                    });
                    let acc3 = bind_accumulator_9(&acc9, &r1);
                    let r2 = on_round(ChainRound::Tail {
                        round: 3 * g + 2,
                        h0: acc3[0],
                        hinf: acc3[2],
                    });
                    core::array::from_fn(|i| {
                        let mut v = eqf(i & 1, &r0);
                        v.mul_assign(&eqf((i >> 1) & 1, &r1));
                        v.mul_assign(&eqf((i >> 2) & 1, &r2));
                        v
                    })
                }
            };

            // separate streaming fold (the measured winning shape) into the
            // next dense arena region; the fold writes every element before
            // anything reads it
            let fold_out = 1usize << (folding_steps - 3 * g - 3);
            let dst_off = if g == 0 { 0 } else { live_off + live_len };
            let neon_folds = match &kernels {
                #[cfg(target_arch = "aarch64")]
                ChainKernels::Neon(_) => true,
                ChainKernels::Generic(_) => false,
            };
            if g == 0 {
                for (i, src) in base_sources.iter().enumerate() {
                    let dst = unsafe {
                        core::slice::from_raw_parts_mut(
                            fold_arena[i].as_mut_ptr() as *mut E,
                            fold_out,
                        )
                    };
                    if neon_folds {
                        #[cfg(target_arch = "aarch64")]
                        lsb_bench::lsb_fold_base_soa_parallel::<F, E>(
                            src.ptr as *const u8,
                            dst,
                            &lw,
                            worker,
                        );
                    } else {
                        lsb_generic::fold_base::<F, E>(src, dst, &lw, worker);
                    }
                }
                for (i, src) in ext_sources.iter().enumerate() {
                    let dst = unsafe {
                        core::slice::from_raw_parts_mut(
                            fold_arena[nb + i].as_mut_ptr() as *mut E,
                            fold_out,
                        )
                    };
                    if neon_folds {
                        #[cfg(target_arch = "aarch64")]
                        lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                            src.ptr as *const u8,
                            dst,
                            &lw,
                            worker,
                        );
                    } else {
                        lsb_generic::fold_ext::<E>(
                            crate::gkr::prover::SendConstPtr(src.ptr as *const E),
                            dst,
                            &lw,
                            worker,
                        );
                    }
                }
            } else {
                for buf in fold_arena.iter_mut() {
                    let base = buf.as_mut_ptr();
                    let src_ptr = unsafe { base.add(live_off) as *const u8 };
                    let dst = unsafe {
                        core::slice::from_raw_parts_mut(base.add(dst_off) as *mut E, fold_out)
                    };
                    if neon_folds {
                        #[cfg(target_arch = "aarch64")]
                        {
                            if fold_out % 4 == 0 {
                                lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                                    src_ptr, dst, &lw, worker,
                                );
                            } else {
                                lsb_bench::lsb_fold_ext_parallel::<E>(src_ptr, dst, &lw, worker);
                            }
                        }
                    } else {
                        lsb_generic::fold_ext::<E>(
                            crate::gkr::prover::SendConstPtr(src_ptr as *const E),
                            dst,
                            &lw,
                            worker,
                        );
                    }
                }
            }
            live_off = dst_off;
            live_len = fold_out;
        }

        // ---- scalar tail rounds: adjacent-pair naive rounds over the live
        // dense tables (parallel over pairs; small tails collapse to a
        // single chunk under the worker threshold) ----
        for t in 0..tail_rounds {
            let pairs = live_len / 2;
            assert_eq!(tail_t_table.len(), pairs);
            let (h0, hinf) = tail_round_message::<F, E>(
                &prog,
                fold_arena,
                live_off,
                pairs,
                tail_t_table,
                worker,
            );
            let r = on_round(ChainRound::Tail {
                round: 3 * num_passes + t,
                h0,
                hinf,
            });
            let dst_off = live_off + live_len;
            tail_fold_tables::<E>(fold_arena, live_off, pairs, dst_off, &r, worker);
            live_off = dst_off;
            live_len = pairs;
            contract_pair_sums(tail_t_table);
        }

        assert_eq!(live_len, 1);
        let mut finals = BTreeMap::new();
        for (i, addr) in base_addrs.iter().chain(ext_addrs.iter()).enumerate() {
            let v = unsafe { *(fold_arena[i].as_ptr().add(live_off) as *const E) };
            finals.insert(*addr, v);
        }
        Some(finals)
    }
}

/// One scalar tail round's message pair `(h(0), leading coefficient)`: the
/// folded program evaluated over the adjacent live pairs of every table,
/// weighted by the contracted suffix eq table. Parallel over pairs; small
/// tails collapse to a single chunk under the worker threshold.
fn tail_round_message<F: PrimeField, E: FieldExtension<F> + Field>(
    prog: &super::program::OwnedSoaProgram<F, E>,
    fold_arena: &[Box<[core::mem::MaybeUninit<E>]>],
    live_off: usize,
    pairs: usize,
    tail_t_table: &[E],
    worker: &Worker,
) -> (E, E) {
    use crate::gkr::prover::SendConstPtr;
    use crate::gkr::PAR_THRESHOLD;

    assert_eq!(tail_t_table.len(), pairs);
    let slot_ptrs: Vec<SendConstPtr<E>> = fold_arena
        .iter()
        .map(|b| SendConstPtr(b.as_ptr() as *const E))
        .collect();
    let num_slots = slot_ptrs.len();

    let geometry = worker.get_geometry_with_threshold(pairs, PAR_THRESHOLD);
    let mut partials: Vec<(E, E)> = vec![(E::ZERO, E::ZERO); geometry.num_chunks];
    worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
        let mut it = partials.iter_mut();
        let slot_ptrs = &slot_ptrs;
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let dst = it.next().unwrap();
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut v0s: Vec<E> = vec![E::ZERO; num_slots];
                let mut dts: Vec<E> = vec![E::ZERO; num_slots];
                let mut form0: Vec<E> = vec![E::ZERO; prog.forms.len()];
                let mut formd: Vec<E> = vec![E::ZERO; prog.forms.len()];
                let (h0, hinf) = dst;
                for j in chunk_start..(chunk_start + chunk_size) {
                    let (g0, ginf) = tail_eval_pair::<F, E>(
                        prog, slot_ptrs, live_off, j, &mut v0s, &mut dts, &mut form0, &mut formd,
                    );
                    let w = tail_t_table[j];
                    let mut t0 = g0;
                    t0.mul_assign(&w);
                    h0.add_assign(&t0);
                    let mut ti = ginf;
                    ti.mul_assign(&w);
                    hinf.add_assign(&ti);
                }
            })
        }
    });

    let mut h0 = E::ZERO;
    let mut hinf = E::ZERO;
    for (p0, pinf) in partials.into_iter() {
        h0.add_assign(&p0);
        hinf.add_assign(&pinf);
    }
    (h0, hinf)
}

/// The folded program's `(G(0), leading coefficient)` on ONE adjacent live
/// pair: linear forms at X = 0 and on the differences, then products and
/// expanded quadratic terms (the affine parts vanish at infinity).
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tail_eval_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    prog: &super::program::OwnedSoaProgram<F, E>,
    slot_ptrs: &[crate::gkr::prover::SendConstPtr<E>],
    live_off: usize,
    j: usize,
    v0s: &mut [E],
    dts: &mut [E],
    form0: &mut [E],
    formd: &mut [E],
) -> (E, E) {
    for (slot, ptr) in slot_ptrs.iter().enumerate() {
        let v0 = unsafe { *ptr.get().add(live_off + 2 * j) };
        let v1 = unsafe { *ptr.get().add(live_off + 2 * j + 1) };
        let mut d = v1;
        d.sub_assign(&v0);
        v0s[slot] = v0;
        dts[slot] = d;
    }
    for (fi, members) in prog.forms.iter().enumerate() {
        let mut a0 = E::ZERO;
        let mut ad = E::ZERO;
        for (op, idx) in members.iter() {
            let (x0, xd) = (v0s[*idx as usize], dts[*idx as usize]);
            match op {
                super::program::FormOp::Add => {
                    a0.add_assign(&x0);
                    ad.add_assign(&xd);
                }
                super::program::FormOp::Sub => {
                    a0.sub_assign(&x0);
                    ad.sub_assign(&xd);
                }
                super::program::FormOp::Mul(c) => {
                    let mut t0 = x0;
                    t0.mul_assign_by_base(c);
                    a0.add_assign(&t0);
                    let mut td = xd;
                    td.mul_assign_by_base(c);
                    ad.add_assign(&td);
                }
            }
        }
        form0[fi] = a0;
        formd[fi] = ad;
    }
    let mut g0 = prog.additive_constant;
    let mut ginf = E::ZERO;
    for (a, f, c) in prog.products.iter() {
        let mut t0 = v0s[*a as usize];
        t0.mul_assign(&form0[*f as usize]);
        t0.mul_assign(c);
        g0.add_assign(&t0);
        let mut ti = dts[*a as usize];
        ti.mul_assign(&formd[*f as usize]);
        ti.mul_assign(c);
        ginf.add_assign(&ti);
    }
    for (a, b, c) in prog.folded_quad.iter() {
        let mut t0 = v0s[*a as usize];
        t0.mul_assign(&v0s[*b as usize]);
        t0.mul_assign(c);
        g0.add_assign(&t0);
        let mut ti = dts[*a as usize];
        ti.mul_assign(&dts[*b as usize]);
        ti.mul_assign(c);
        ginf.add_assign(&ti);
    }
    for (i, c) in prog.folded_lin.iter() {
        let mut t0 = v0s[*i as usize];
        t0.mul_assign(c);
        g0.add_assign(&t0);
    }
    (g0, ginf)
}

/// Folds every live table by `(1 - r, r)` over adjacent pairs into the next
/// dense arena region. Parallel over pairs; the destination region is
/// disjoint from the live one.
fn tail_fold_tables<E: Field>(
    fold_arena: &mut [Box<[core::mem::MaybeUninit<E>]>],
    live_off: usize,
    pairs: usize,
    dst_off: usize,
    r: &E,
    worker: &Worker,
) {
    use crate::gkr::prover::SendPtr;
    use crate::gkr::PAR_THRESHOLD;

    for buf in fold_arena.iter_mut() {
        let base = SendPtr(buf.as_mut_ptr() as *mut E);
        worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
            for thread_idx in 0..geometry.num_chunks {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let bp = base.get();
                    for j in chunk_start..(chunk_start + chunk_size) {
                        let v0 = unsafe { *bp.add(live_off + 2 * j) };
                        let v1 = unsafe { *bp.add(live_off + 2 * j + 1) };
                        let mut v = v1;
                        v.sub_assign(&v0);
                        v.mul_assign(r);
                        v.add_assign(&v0);
                        unsafe {
                            bp.add(dst_off + j).write(v);
                        }
                    }
                })
            }
        });
    }
}

/// Contracts an eq suffix table by summing out its lowest variable:
/// `t[j] = t[2j] + t[2j+1]`, halving the length (no-op at length 1).
fn contract_pair_sums<E: Field>(table: &mut Vec<E>) {
    let pairs = table.len() / 2;
    if pairs == 0 {
        return;
    }
    for j in 0..pairs {
        let mut v = table[2 * j];
        v.add_assign(&table[2 * j + 1]);
        table[j] = v;
    }
    table.truncate(pairs);
}
