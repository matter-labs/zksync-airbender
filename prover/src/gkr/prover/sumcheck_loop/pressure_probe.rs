//! Same-size sumcheck PRESSURE PROBE (aarch64, BabyBear/Ext4 only).
//!
//! Investigation tool: times one layer's window-3 INITIAL pass, its fold and
//! the first CONTINUING pass over RANDOM data, split (a) by kernel phase
//! (fill base / fill ext / forms / base products / ext steps / eq) through
//! the `PH_*` masks of `lsb_soa_full_parallel`, and (b) by GATE CLASS: the
//! program is rebuilt from a filtered gate list ("only class X" and "all but
//! class X"), so the marginal and standalone cost of every class — including
//! the slot fills only it needs — is measured, not modeled. Also reports a
//! plain streaming-read reference over the same bytes so each pass can be
//! placed against the memory bound.
//!
//! No proof is produced; the proof bytes of the real prover are untouched
//! (nothing outside this module changes). `#[ignore]`d, env-driven:
//!
//! ```text
//! PRESSURE_LOG2=23 PRESSURE_THREADS=8 PRESSURE_LAYERS=0,1 \
//!   cargo test --release -p prover --lib -- --ignored --nocapture --exact \
//!   gkr::prover::sumcheck_loop::pressure_probe::same_size_pressure_probe
//! ```
//!
//! Env: `PRESSURE_LOG2` (trace length log2, default 23), `PRESSURE_THREADS`
//! (default 8), `PRESSURE_LAYERS` (comma list, default `0,1`),
//! `PRESSURE_CIRCUIT` (artifact stem, default `unified_extended_machine`),
//! `PRESSURE_REPS` (default 2, min is reported), `PRESSURE_CLASSES=0` skips
//! the per-class variants.

use super::kernel_collector::KernelCollector;
use super::windowed_mode::full_size_scratch::produce_descriptions_from_batched_description;
use super::windowed_mode::lsb_bench::{
    self, PH_ALL, PH_EXT, PH_FILL_BASE, PH_FILL_EXT, PH_FORMS, PH_LAZY,
};
use super::windowed_mode::lsb_chain::quasi;
use super::windowed_mode::program::{build_soa_program, FormRef, OwnedSoaProgram, ProgramStep};
use super::SameSizeChainOps;
use crate::gkr::prover::gkr_backend::{GKRBackend, NeonGKRBackend};
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::evaluation_kernels::BatchedGKRTermDescriptionConstants;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription, GKRRelation};
use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use field::Field;
use std::time::{Duration, Instant};
use worker::Worker;

type BB = BabyBearField;
type E4 = BabyBearExt4;

const P: u64 = 0x7800_0001;

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// splitmix64 stream: fast, deterministic, good enough for timing data.
fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn par_fill<T: Send, const K: usize>(
    dst: &mut [T],
    seed: u64,
    threads: usize,
    make: impl Fn([u32; K]) -> T + Sync,
) {
    let chunk = dst.len().div_ceil(threads).max(1);
    std::thread::scope(|s| {
        for (i, part) in dst.chunks_mut(chunk).enumerate() {
            let make = &make;
            s.spawn(move || {
                let mut st = seed ^ ((i as u64 + 1) << 40);
                for el in part.iter_mut() {
                    let limbs: [u32; K] = core::array::from_fn(|_| (splitmix(&mut st) % P) as u32);
                    *el = make(limbs);
                }
            });
        }
    });
}

fn random_base_polys(count: usize, len: usize, threads: usize, seed: u64) -> Vec<Vec<BB>> {
    (0..count)
        .map(|i| {
            let mut v = vec![BB::ZERO; len];
            par_fill::<BB, 1>(&mut v, seed ^ (i as u64 * 0x1234_5678_9ABC), threads, |l| {
                BB::new(l[0])
            });
            v
        })
        .collect()
}

fn random_ext_polys(count: usize, len: usize, threads: usize, seed: u64) -> Vec<Vec<E4>> {
    (0..count)
        .map(|i| {
            let mut v = vec![E4::ZERO; len];
            par_fill::<E4, 4>(&mut v, seed ^ (i as u64 * 0xABCD_EF01_2345), threads, |l| {
                E4::from_array_of_base(l.map(BB::new))
            });
            v
        })
        .collect()
}

fn random_ext_scalar(st: &mut u64) -> E4 {
    E4::from_array_of_base(core::array::from_fn(|_| BB::new((splitmix(st) % P) as u32)))
}

/// Gate classes the probe splits the layer by.
fn gate_class(rel: &GKRRelation<BB>) -> &'static str {
    use GKRRelation::*;
    match rel {
        MaxQuadratic { .. } | LinearBaseFieldRelation { .. } => "next_layer_quadratic",
        EnforceSingleMaxQuadraticConstraint { .. } | EnforceConstraintsMaxQuadratic { .. } => {
            "assert_zero"
        }
        CopyInBaseField { .. } | CopyInExtensionField { .. } => "copies",
        InitialGrandProductFromCaches { .. }
        | TrivialProduct { .. }
        | MaskIntoIdentityProduct { .. }
        | UnbalancedGrandProductWithCache { .. } => "ext_products",
        InitsOrTeardownsInitialPair { .. }
        | InitialGrandProductWithoutCaches { .. }
        | MaterializeGrandProductTermExpression { .. } => "memory_base_products",
        LookupWithCachedDensAndSetup { .. }
        | LookupPairFromCachedVectorInputs { .. }
        | AggregateLookupRationalPair { .. }
        | LookupPairFromMaterializedVectorInputs { .. }
        | LookupFromMaterializedVectorInputWithSetup { .. }
        | LookupUnbalancedPairWithMaterializedVectorInputs { .. }
        | LookupPairFromVectorInputs { .. }
        | LookupFromVectorInputWithSetup { .. }
        | LookupUnbalancedPairWithVectorInputs { .. }
        | MaterializedVectorLookupInput { .. } => "lookups_ext",
        _ => "lookups_base",
    }
}

fn filtered_layer(
    layer: &GKRLayerDescription<BB>,
    keep: impl Fn(&GKRRelation<BB>) -> bool,
) -> GKRLayerDescription<BB> {
    let mut l = layer.clone();
    l.gates = layer
        .gates
        .iter()
        .filter(|g| keep(&g.enforced_relation))
        .cloned()
        .collect();
    l.gates_with_external_connections = layer
        .gates_with_external_connections
        .iter()
        .filter(|g| keep(&g.enforced_relation))
        .cloned()
        .collect();
    l
}

struct Challenges {
    cc: BatchedGKRTermDescriptionConstants<BB, E4>,
    batch_base: E4,
    top_bits: Vec<u32>,
    shift: u32,
}

fn build_program(
    layer: &GKRLayerDescription<BB>,
    layer_idx: usize,
    ch: &Challenges,
) -> (OwnedSoaProgram<BB, E4>, Vec<GKRAddress>, Vec<GKRAddress>) {
    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        ch.batch_base,
        ch.cc.lookup_challenges_multiplicative_part,
        ch.cc.lookup_challenges_additive_part,
        &ch.top_bits,
        ch.shift,
    );
    let description = collector.make_batched_description(&ch.cc, layer_idx);
    let (_compact, base_addrs, ext_addrs) =
        produce_descriptions_from_batched_description(&description);
    let prog = build_soa_program(
        &description,
        &collector,
        layer,
        &ch.cc,
        &base_addrs,
        &ext_addrs,
    );
    (prog, base_addrs, ext_addrs)
}

fn prog_stats(prog: &OwnedSoaProgram<BB, E4>) -> String {
    let (mut qbb, mut qbe, mut qee, mut lb, mut le) = (0, 0, 0, 0, 0);
    for s in prog.rest_steps.iter() {
        match s {
            ProgramStep::QuadBB { .. } => qbb += 1,
            ProgramStep::QuadBE { .. } => qbe += 1,
            ProgramStep::QuadEE { .. } => qee += 1,
            ProgramStep::LinB { .. } => lb += 1,
            ProgramStep::LinE { .. } => le += 1,
        }
    }
    let form_members: usize = prog.forms.iter().map(|f| f.members.len()).sum();
    let prod_form_operands = prog
        .products
        .iter()
        .flat_map(|(a, b, _)| [a, b])
        .filter(|r| matches!(r, FormRef::Form(_)))
        .count();
    // operand sharing: products grouped by their most frequent operand
    // (greedy: a product joins the group of whichever operand is more shared)
    let key = |r: &FormRef| match r {
        FormRef::Slot(i) => *i as usize,
        FormRef::Form(i) => 1 << 16 | *i as usize,
    };
    let mut freq: std::collections::BTreeMap<usize, usize> = Default::default();
    for (a, b, _) in prog.products.iter() {
        *freq.entry(key(a)).or_default() += 1;
        *freq.entry(key(b)).or_default() += 1;
    }
    let mut groups: std::collections::BTreeMap<usize, usize> = Default::default();
    for (a, b, _) in prog.products.iter() {
        let (ka, kb) = (key(a), key(b));
        let k = if freq[&ka] >= freq[&kb] { ka } else { kb };
        *groups.entry(k).or_default() += 1;
    }
    let shared_groups = groups.values().filter(|m| **m >= 2).count();
    let saved_muls: usize = groups.values().filter(|m| **m >= 2).map(|m| m - 1).sum();
    let max_group = groups.values().copied().max().unwrap_or(0);
    format!(
        "nb={} (interp {}) ne={} (interp {}) | forms={} (members {}) products={} (form operands {}; sharing: {} groups of >=2 covering {} products, max {}, {} muls saveable) | rest: QuadBB {} QuadBE {} QuadEE {} LinB {} LinE {}",
        prog.base_interp.len(),
        prog.base_interp.iter().filter(|b| **b).count(),
        prog.ext_interp.len(),
        prog.ext_interp.iter().filter(|b| **b).count(),
        prog.forms.len(),
        form_members,
        prog.products.len(),
        prod_form_operands,
        shared_groups,
        saved_muls + shared_groups,
        max_group,
        saved_muls,
        qbb,
        qbe,
        qee,
        lb,
        le
    )
}

fn time_min<T>(reps: usize, mut f: impl FnMut() -> T) -> (Duration, T) {
    let mut best = Duration::MAX;
    let mut out = None;
    for _ in 0..reps.max(1) {
        let t = Instant::now();
        let r = f();
        let d = t.elapsed();
        if d < best {
            best = d;
        }
        out = Some(r);
    }
    (best, out.unwrap())
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

/// Plain parallel streaming read of the given byte ranges (xor-reduce), the
/// memory-side reference for the fill phases.
fn stream_read_ms(base: &[&[BB]], ext: &[&[E4]], threads: usize, reps: usize) -> (f64, f64) {
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    for b in base {
        ranges.push((b.as_ptr() as usize, b.len()));
    }
    for e in ext {
        ranges.push((e.as_ptr() as usize, e.len() * 4));
    }
    let total_bytes: usize = ranges.iter().map(|(_, n)| n * 4).sum();
    // split every poly into `threads` pieces so all threads stream concurrently
    let (d, _) = time_min(reps, || {
        let acc = std::sync::atomic::AtomicU32::new(0);
        std::thread::scope(|s| {
            for t in 0..threads {
                let ranges = &ranges;
                let acc = &acc;
                s.spawn(move || {
                    let mut x = 0u32;
                    for (p, n) in ranges.iter() {
                        let chunk = n.div_ceil(threads);
                        let start = (t * chunk).min(*n);
                        let end = ((t + 1) * chunk).min(*n);
                        let sl = unsafe {
                            core::slice::from_raw_parts((*p as *const u32).add(start), end - start)
                        };
                        for w in sl.chunks_exact(8) {
                            x ^= w[0] ^ w[1] ^ w[2] ^ w[3] ^ w[4] ^ w[5] ^ w[6] ^ w[7];
                        }
                    }
                    acc.fetch_xor(x, std::sync::atomic::Ordering::Relaxed);
                });
            }
        });
        std::hint::black_box(acc.load(std::sync::atomic::Ordering::Relaxed));
    });
    (ms(d), total_bytes as f64 / d.as_secs_f64() / 1e9)
}

struct Data {
    base: Vec<Vec<BB>>,
    ext: Vec<Vec<E4>>,
    eq_suffix: Vec<E4>,
    eq_suffix_next: Vec<E4>,
    weights: [E4; 8],
    rows: usize,
}

/// Times every stage of one program over the first nb/ne polys of the pool.
fn measure_variant(
    tag: &str,
    layer: &GKRLayerDescription<BB>,
    layer_idx: usize,
    ch: &Challenges,
    data: &Data,
    worker: &Worker,
    threads: usize,
    reps: usize,
    phases: bool,
) {
    let (prog, base_addrs, ext_addrs) = build_program(layer, layer_idx, ch);
    let nb = base_addrs.len();
    let ne = ext_addrs.len();
    assert!(
        nb <= data.base.len() && ne <= data.ext.len(),
        "pool too small"
    );
    let rows = data.rows;
    let base_refs: Vec<&[BB]> = data.base[..nb].iter().map(|v| &v[..]).collect();
    let ext_refs: Vec<&[E4]> = data.ext[..ne].iter().map(|v| &v[..]).collect();
    let gates = layer.gates.len() + layer.gates_with_external_connections.len();
    println!("[pressure] {tag}: {gates} gates, {}", prog_stats(&prog));

    let (sread_ms, gbs) = stream_read_ms(&base_refs, &ext_refs, threads, reps);
    println!(
        "[pressure] {tag}: streaming read of all inputs {:.1} ms ({:.1} GB/s, {:.2} GB)",
        sread_ms,
        gbs,
        (nb * rows * 8 * 4 + ne * rows * 8 * 16) as f64 / 1e9
    );

    let mut full_ref: Option<[E4; 27]> = None;
    if phases {
        let masks: [(&str, u32); 6] = [
            ("fill_base", PH_FILL_BASE),
            ("+fill_ext", PH_FILL_BASE | PH_FILL_EXT),
            ("+forms", PH_FILL_BASE | PH_FILL_EXT | PH_FORMS),
            (
                "+base_products(lazy)",
                PH_FILL_BASE | PH_FILL_EXT | PH_FORMS | PH_LAZY,
            ),
            (
                "+ext_steps",
                PH_FILL_BASE | PH_FILL_EXT | PH_FORMS | PH_LAZY | PH_EXT,
            ),
            ("+eq(all)", PH_ALL),
        ];
        let bq = quasi::<BB, false>(&base_refs);
        let eq = quasi::<E4, false>(&ext_refs);
        let unroll = env_usize("PRESSURE_U", 2);
        let mut prev = 0.0f64;
        for (name, mask) in masks {
            let run = |mask: u32| {
                macro_rules! go {
                    ($u:literal) => {
                        lsb_bench::lsb_soa_full_parallel::<BB, E4, 7, 2, 27, $u>(
                            &bq,
                            &eq,
                            &prog.base_interp,
                            &prog.ext_interp,
                            None,
                            &prog.forms,
                            &prog.products,
                            &prog.rest_steps,
                            &prog.additive_constant,
                            &data.eq_suffix,
                            rows,
                            worker,
                            mask,
                        )
                    };
                }
                match unroll {
                    1 => go!(1),
                    4 => go!(4),
                    _ => go!(2),
                }
            };
            let (d, res) = time_min(reps, || run(mask));
            if mask == PH_ALL {
                full_ref = Some(res);
            }
            let cur = ms(d);
            println!(
                "[pressure] {tag}: initial pass phases (U={unroll}) {name:>22}: cumulative {cur:8.1} ms, delta {:8.1} ms",
                cur - prev
            );
            prev = cur;
        }
    }

    // folds: every slot into an ext table of `rows` entries (independent of the program)
    let mut folded: Vec<Vec<E4>> = (0..nb + ne).map(|_| vec![E4::ZERO; rows]).collect();
    let (d_fold, _) = time_min(reps, || {
        for (i, src) in base_refs.iter().enumerate() {
            lsb_bench::lsb_fold_base_soa_parallel::<BB, E4>(
                src.as_ptr() as *const u8,
                &mut folded[i],
                &data.weights,
                worker,
            );
        }
        for (i, src) in ext_refs.iter().enumerate() {
            lsb_bench::lsb_fold_ext_soa_parallel::<E4>(
                src.as_ptr() as *const u8,
                &mut folded[nb + i],
                &data.weights,
                worker,
            );
        }
    });
    let fold_bytes = (nb * rows * 8 * 4 + ne * rows * 8 * 16 + (nb + ne) * rows * 16) as f64;
    println!(
        "[pressure] {tag}: fold initial {:.1} ms ({:.1} GB/s read+write)",
        ms(d_fold),
        fold_bytes / d_fold.as_secs_f64() / 1e9
    );
    let folded_refs_pre: Vec<&[E4]> = folded.iter().map(|v| &v[..]).collect();
    // reference continuing pass through the lsb_bench kernel (program still owned here)
    let cont_ref: Option<[E4; 27]> = phases.then(|| {
        let folded_interp: Vec<bool> = prog
            .base_interp
            .iter()
            .chain(prog.ext_interp.iter())
            .copied()
            .collect();
        let srcs = quasi::<E4, false>(&folded_refs_pre);
        let (d, r) = time_min(reps, || {
            lsb_bench::lsb_soa_ext_pass_parallel::<BB, E4, 7, 2, 27, 2>(
                &srcs,
                &folded_interp,
                None,
                &prog.forms,
                &prog.products,
                &prog.folded_quad,
                &prog.folded_lin,
                &prog.additive_constant,
                &data.eq_suffix_next,
                rows / 8,
                worker,
            )
        });
        println!(
            "[pressure] {tag}: continuing pass 1 (lsb_bench kernel) {:.1} ms",
            ms(d)
        );
        core::array::from_fn(|g| r[lsb_bench::w3_soa_cell_of_generic(g)])
    });
    drop(folded_refs_pre);

    if phases {
        // skeleton: the same program with every term removed = grid fills +
        // forms + eq only, through the backend kernels
        let (mut skel, _, _) = build_program(layer, layer_idx, ch);
        skel.products.clear();
        skel.rest_steps.clear();
        skel.folded_quad.clear();
        skel.folded_lin.clear();
        let skel_chain = NeonGKRBackend.make_same_size_chain(skel);
        let (d, _) = time_min(reps, || {
            skel_chain.window_initial_pass(&base_refs, &ext_refs, &data.eq_suffix, rows, worker)
        });
        println!(
            "[pressure] {tag}: initial pass SKELETON (fills + forms + eq, no terms) {:.1} ms",
            ms(d)
        );
        let fr: Vec<&[E4]> = folded.iter().map(|v| &v[..]).collect();
        let (d, _) = time_min(reps, || {
            skel_chain.window_continuing_pass(&fr, &data.eq_suffix_next, rows / 8, worker)
        });
        println!(
            "[pressure] {tag}: continuing pass 1 SKELETON (fills + forms + eq, no terms) {:.1} ms",
            ms(d)
        );
    }

    let backend = NeonGKRBackend;
    let chain = backend.make_same_size_chain(prog);
    let (d_init, chain_res) = time_min(reps, || {
        chain.window_initial_pass(&base_refs, &ext_refs, &data.eq_suffix, rows, worker)
    });
    if let Some(r) = full_ref {
        let perm: [E4; 27] = core::array::from_fn(|g| r[lsb_bench::w3_soa_cell_of_generic(g)]);
        assert_eq!(
            perm, chain_res,
            "{tag}: chain initial pass diverged from the lsb_bench kernel"
        );
        println!("[pressure] {tag}: A/B chain vs lsb_bench kernel: identical");
    }
    println!(
        "[pressure] {tag}: initial pass (chain) {:.1} ms = {:.1} ns per row-thread ({} rows x {} thr)",
        ms(d_init),
        d_init.as_secs_f64() * 1e9 * threads as f64 / rows as f64,
        rows,
        threads
    );

    let folded_refs: Vec<&[E4]> = folded.iter().map(|v| &v[..]).collect();
    let (d_cont, cont_res) = time_min(reps, || {
        chain.window_continuing_pass(&folded_refs, &data.eq_suffix_next, rows / 8, worker)
    });
    if let Some(r) = cont_ref {
        assert_eq!(
            r, cont_res,
            "{tag}: chain continuing pass diverged from the lsb_bench kernel"
        );
        println!("[pressure] {tag}: A/B continuing chain vs lsb_bench kernel: identical");
    }
    println!(
        "[pressure] {tag}: continuing pass 1 {:.1} ms ({} rows of 8 ext; {:.1} GB/s read; geometric total of all continuing passes ~ x1.14)",
        ms(d_cont),
        rows / 8,
        ((nb + ne) * rows * 16) as f64 / d_cont.as_secs_f64() / 1e9
    );
}

#[test]
#[ignore]
fn same_size_pressure_probe() {
    let log2 = env_usize("PRESSURE_LOG2", 23);
    let threads = env_usize("PRESSURE_THREADS", 8);
    let reps = env_usize("PRESSURE_REPS", 2);
    let classes = env_usize("PRESSURE_CLASSES", 1) != 0;
    let layers: Vec<usize> = std::env::var("PRESSURE_LAYERS")
        .unwrap_or_else(|_| "0,1".to_string())
        .split(',')
        .filter_map(|s| s.trim().parse().ok())
        .collect();
    let circuit =
        std::env::var("PRESSURE_CIRCUIT").unwrap_or_else(|_| "unified_extended_machine".into());
    let path = std::env::var("PRESSURE_CIRCUIT_PATH")
        .unwrap_or_else(|_| format!("../cs/compiled_circuits/{circuit}_layout_gkr.json"));
    let file = std::fs::File::open(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let artifact: GKRCircuitArtifact<BB> =
        serde_json::from_reader(std::io::BufReader::new(file)).expect("artifact");
    println!(
        "[pressure] circuit {circuit}: artifact trace_len 2^{}, probing at 2^{log2}, {threads} threads, {reps} reps",
        artifact.trace_len.trailing_zeros()
    );

    let worker = Worker::new_with_num_threads(threads);
    let trace_len = 1usize << log2;
    let rows = trace_len >> 3;

    let mut st = 0xC0FFEE_u64;
    let r = |st: &mut u64| random_ext_scalar(st);
    let ch = Challenges {
        cc: BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges {
                permutation_argument_linearization_challenges: core::array::from_fn(|_| r(&mut st)),
                permutation_argument_additive_part: r(&mut st),
                _marker: core::marker::PhantomData,
            },
            lookup_challenges_multiplicative_part: r(&mut st),
            lookup_challenges_additive_part: r(&mut st),
            _marker: core::marker::PhantomData,
        },
        batch_base: r(&mut st),
        top_bits: (0..256).map(|i| (i % 7) as u32).collect(),
        shift: crate::gkr::high_bits_offset_for_inits_and_teardowns::<2>(trace_len),
    };

    // the data pool: the widest layer's slot counts
    let mut max_nb = 0;
    let mut max_ne = 0;
    for &li in layers.iter() {
        let (_p, b, e) = build_program(&artifact.layers[li], li, &ch);
        max_nb = max_nb.max(b.len());
        max_ne = max_ne.max(e.len());
    }
    let t = Instant::now();
    let data = Data {
        base: random_base_polys(max_nb, trace_len, threads, 11),
        ext: random_ext_polys(max_ne, trace_len, threads, 13),
        eq_suffix: (0..rows).map(|_| r(&mut st)).collect(),
        eq_suffix_next: (0..rows / 8).map(|_| r(&mut st)).collect(),
        weights: core::array::from_fn(|_| r(&mut st)),
        rows,
    };
    println!(
        "[pressure] random pool: {max_nb} base + {max_ne} ext polys of 2^{log2} built in {:.1} s",
        t.elapsed().as_secs_f64()
    );

    for &li in layers.iter() {
        let layer = &artifact.layers[li];
        println!("[pressure] ===== layer {li} =====");
        measure_variant(
            &format!("L{li} full"),
            layer,
            li,
            &ch,
            &data,
            &worker,
            threads,
            reps,
            true,
        );
        if !classes {
            continue;
        }
        let mut present: Vec<&'static str> = Vec::new();
        for g in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            let c = gate_class(&g.enforced_relation);
            if !present.contains(&c) {
                present.push(c);
            }
        }
        for c in present.iter() {
            let only = filtered_layer(layer, |rel| gate_class(rel) == *c);
            measure_variant(
                &format!("L{li} only {c}"),
                &only,
                li,
                &ch,
                &data,
                &worker,
                threads,
                reps,
                false,
            );
            let without = filtered_layer(layer, |rel| gate_class(rel) != *c);
            let remaining = without.gates.len() + without.gates_with_external_connections.len();
            if remaining > 0 {
                measure_variant(
                    &format!("L{li} without {c}"),
                    &without,
                    li,
                    &ch,
                    &data,
                    &worker,
                    threads,
                    reps,
                    false,
                );
            }
        }
    }
}
