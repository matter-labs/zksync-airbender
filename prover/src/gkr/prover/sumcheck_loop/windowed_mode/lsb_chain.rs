//! Production driver for the UNFUSED LSB uniskip chain over a same-size
//! layer: every pass emits one 16-point univariate covering 3 variables
//! (bound LSB-first, so all reads are groups of 8 consecutive elements),
//! then a separate streaming fold binds the drawn challenge's Lagrange
//! weights. Kernels are the `lsb_bench` set validated by the chain test.
//!
//! Architecture contract: this module COMPUTES only. The transcript
//! (commit/draw), claim chaining, and all self-checks live at the caller,
//! which supplies `on_pass` -- called with each pass's 16 evaluations and
//! returning the drawn folding challenge -- and the per-pass eq suffix
//! tables (orientation conventions stay at the caller).

use std::collections::BTreeMap;

use super::bench::build_soa_program;
use super::full_size_scratch::produce_descriptions_from_batched_description;
use super::lsb_bench::{self, LsbLdeAny, PH_ALL};
use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelCollector;
use crate::gkr::sumcheck::access_and_fold::{DisjointAccessQuasiSlice, GKRStorage};
use crate::gkr::sumcheck::evaluation_kernels::BatchedGKRTermDescriptionConstants;
use crate::worker::Worker;
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};

/// Runs the chain; `None` means the platform/shape fast path does not apply
/// (caller falls back). On success returns the per-input final evaluations
/// (each poly folded by all passes' challenge weights).
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_lsb_uniskip_chain<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    OnPass: FnMut(usize, &[E; 16]) -> E,
>(
    collector: &KernelCollector<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    gkr_storage: &mut GKRStorage<F, E>,
    folding_steps: usize,
    eq_suffixes: &[Box<[E]>],
    fold_arena: &mut [Box<[core::mem::MaybeUninit<E>]>],
    worker: &Worker,
    mut on_pass: OnPass,
) -> Option<BTreeMap<GKRAddress, E>>
where
    [(); E::DEGREE]: Sized,
{
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = (
            collector,
            challenge_constants,
            gkr_storage,
            folding_steps,
            eq_suffixes,
            fold_arena,
            worker,
            &mut on_pass,
        );
        None
    }

    #[cfg(target_arch = "aarch64")]
    {
        use super::neon;
        if const { !neon::is_bb_pair::<F, E>() } {
            return None;
        }
        if folding_steps % 3 != 0 || folding_steps < 6 {
            return None;
        }
        let num_passes = folding_steps / 3;
        assert_eq!(eq_suffixes.len(), num_passes);

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

        let omega16_bb =
            ::fft::domain_generator_for_size::<::field::baby_bear::base::BabyBearField>(16);
        let mut omega8_bb = omega16_bb;
        omega8_bb.square();
        let omega16_f: F = unsafe { *(&omega16_bb as *const _ as *const F) };
        let lde_tables = LsbLdeAny::K8Mat(neon::LsbLde8MatTables::new(omega8_bb, omega16_bb));
        let mat_tables = match &lde_tables {
            LsbLdeAny::K8Mat(t) => *t,
            _ => unreachable!(),
        };
        let _ = mat_tables; // ext pass takes the enum; kept for clarity

        let nb = base_sources.len();
        let m = 1usize << folding_steps;
        // caller-provided fold arena, one buffer per input poly in
        // base-then-ext order; the chain's dense fold outputs live in
        // consecutive regions (m/8 + m/64 + ... < 3/2 * m/8 elements)
        assert_eq!(fold_arena.len(), nb + ext_sources.len());
        for b in fold_arena.iter() {
            assert!(b.len() >= m / 8 + m / 16);
        }
        let mut live_off = 0usize;
        let mut live_len = 0usize;
        let mut srcs: Vec<DisjointAccessQuasiSlice<E, false>> =
            Vec::with_capacity(fold_arena.len());

        for g in 0..num_passes {
            let out_size = 1usize << (folding_steps - 3 * g - 3);
            assert_eq!(eq_suffixes[g].len(), out_size.max(1));

            let q: [E; 16] = if g == 0 {
                lsb_bench::lsb_soa_full_parallel::<F, E, 4, 4, 16, 2>(
                    &base_sources,
                    &ext_sources,
                    &prog.base_interp,
                    &prog.ext_interp,
                    Some(&lde_tables),
                    &prog.forms,
                    &prog.products,
                    &prog.rest_steps,
                    &prog.additive_constant,
                    &eq_suffixes[g],
                    out_size,
                    worker,
                    PH_ALL,
                )
            } else {
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
                if out_size % 2 == 0 {
                    lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 2>(
                        &srcs,
                        &prog.forms,
                        &prog.products,
                        &prog.folded_quad,
                        &prog.folded_lin,
                        &prog.additive_constant,
                        &lde_tables,
                        &eq_suffixes[g],
                        out_size,
                        worker,
                    )
                } else {
                    lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 1>(
                        &srcs,
                        &prog.forms,
                        &prog.products,
                        &prog.folded_quad,
                        &prog.folded_lin,
                        &prog.additive_constant,
                        &lde_tables,
                        &eq_suffixes[g],
                        out_size,
                        worker,
                    )
                }
            };

            // caller owns transcript + self-checks; it hands back the drawn r
            let r = on_pass(g, &q);
            let lw = super::uniskip::uniskip8_fold_weights::<F, E>(&r, omega16_f);

            // separate streaming fold (the measured winning shape) into the
            // next dense arena region; the fold writes every element before
            // anything reads it
            let fold_out = 1usize << (folding_steps - 3 * g - 3);
            let dst_off = if g == 0 { 0 } else { live_off + live_len };
            if g == 0 {
                for (i, src) in base_sources.iter().enumerate() {
                    let dst = unsafe {
                        core::slice::from_raw_parts_mut(
                            fold_arena[i].as_mut_ptr() as *mut E,
                            fold_out,
                        )
                    };
                    lsb_bench::lsb_fold_base_soa_parallel::<F, E>(
                        src.ptr as *const u8,
                        dst,
                        &lw,
                        worker,
                    );
                }
                for (i, src) in ext_sources.iter().enumerate() {
                    let dst = unsafe {
                        core::slice::from_raw_parts_mut(
                            fold_arena[nb + i].as_mut_ptr() as *mut E,
                            fold_out,
                        )
                    };
                    lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                        src.ptr as *const u8,
                        dst,
                        &lw,
                        worker,
                    );
                }
            } else {
                for buf in fold_arena.iter_mut() {
                    let base = buf.as_mut_ptr();
                    let src_ptr = unsafe { base.add(live_off) as *const u8 };
                    let dst = unsafe {
                        core::slice::from_raw_parts_mut(base.add(dst_off) as *mut E, fold_out)
                    };
                    if fold_out % 4 == 0 {
                        lsb_bench::lsb_fold_ext_soa_parallel::<E>(src_ptr, dst, &lw, worker);
                    } else {
                        lsb_bench::lsb_fold_ext_parallel::<E>(src_ptr, dst, &lw, worker);
                    }
                }
            }
            live_off = dst_off;
            live_len = fold_out;
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
