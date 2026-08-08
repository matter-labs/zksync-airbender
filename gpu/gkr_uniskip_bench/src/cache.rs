//! Host lowering of the fused-cached mode's fixed shared-memory assignment.
//!
//! The pool is `UNISKIP_CACHE_UNITS` fixed units of one `bf` coset slab each
//! (`UNISKIP_TAPS` coset cells by `UNISKIP_ROWS_PER_BLOCK` rows). A source occupies
//! `component_width` consecutive units, so a slab's byte cost is exactly proportional
//! to its width and the plan is a pure greedy — no eviction, no per-tile decisions.
//!
//! What the assignment buys, per logical row, counted in 16-tap `bf`-limb dots:
//! an uncached source costs `ref_count * width` of them (one per reference per coset
//! cell) and a cached one costs `width` — the fill itself is one production per cell.
//! So the resolver work is proportional to `C + Ru`, which is what
//! [`CachePlan::cached_width`] / [`CachePlan::uncached_refs`] report.

use std::fmt;

use crate::abi::*;
use crate::synth::SynthProgram;

/// One cached source's fixed assignment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CacheSlot {
    pub source: u16,
    /// First pool unit of the slab.
    pub unit: u8,
    /// Units it occupies — the source's component width.
    pub width: u32,
    /// Lowered accessor invocations naming this source.
    pub refs: u32,
}

/// The lowered plan: fixed slot assignment plus the census the Task 3 gate reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CachePlan {
    /// Cached sources in slot order.
    pub slots: Vec<CacheSlot>,
    /// Per source: first pool unit, or [`UNISKIP_CACHE_SLOT_NONE`].
    pub source_slot: Vec<u8>,
    /// INVERSE plan the tile fill iterates: unit -> `source | limb << 8`, or
    /// [`UNISKIP_CACHE_FILL_NONE`] for a free unit. The fill walks units, never the
    /// source table.
    pub fill: [u16; UNISKIP_CACHE_UNITS],
    pub units_used: u32,
    /// `C` — sum of `component_width` over CACHED sources.
    pub cached_width: u32,
    /// `Ru` — sum of `ref_count * component_width` over UNCACHED sources.
    pub uncached_refs: u32,
    /// `C + Ru` with an empty plan: sum of `ref_count * component_width` over all
    /// sources, i.e. the Task 1 recompute arm.
    pub baseline: u32,
}

/// Mul-pipe op counts of one 16-tap `bf`-limb dot in the shipped chunked form
/// (`UNISKIP_DOT_CHUNK` = 4): `UNISKIP_TAPS` `mad_wide`, plus
/// `UNISKIP_TAPS / UNISKIP_DOT_CHUNK` `red_wide` at three mul-pipe ops each
/// (`mul_lo` + `mad_lo_cc` + `madc_hi_cc`). The `bf::add`s between chunks are ALU.
pub const DOT_MUL_PIPE_OPS: u32 = UNISKIP_TAPS as u32 + 3 * (UNISKIP_TAPS as u32 / 4);
/// Mul-pipe ops the per-tap address chain adds to a resolution that loads its taps
/// from global: one `IMAD.WIDE` element-index scale per load, and ptxas does not
/// strength-reduce it (see `iteration_times.md`, F9).
pub const TAP_ADDRESS_MUL_PIPE_OPS: u32 = UNISKIP_TAPS as u32;

impl CachePlan {
    /// `C + Ru` — the resolver work the plan leaves, in 16-tap `bf`-limb dots per
    /// logical row per coset cell.
    pub fn resolver_dots(&self) -> u32 {
        self.cached_width + self.uncached_refs
    }

    /// Resolver work as a fraction of the uncached (Task 1) arm.
    pub fn resolver_ratio(&self) -> f64 {
        f64::from(self.resolver_dots()) / f64::from(self.baseline.max(1))
    }

    /// Mul-pipe ops the FILL costs per logical row: every cached unit produces all
    /// `UNISKIP_TAPS` coset cells, and being row-shaped it pays the tap address chain
    /// once for the whole slab instead of once per cell.
    pub fn fill_mul_pipe_ops(&self) -> u64 {
        u64::from(self.cached_width)
            * (u64::from(UNISKIP_TAPS as u32) * u64::from(DOT_MUL_PIPE_OPS)
                + u64::from(TAP_ADDRESS_MUL_PIPE_OPS))
    }

    /// Mul-pipe ops the UNCACHED recompute costs per logical row: each reference
    /// resolves all `UNISKIP_TAPS` coset cells independently and reloads its taps for
    /// every one of them.
    pub fn uncached_mul_pipe_ops(&self) -> u64 {
        u64::from(self.uncached_refs)
            * u64::from(UNISKIP_TAPS as u32)
            * u64::from(DOT_MUL_PIPE_OPS + TAP_ADDRESS_MUL_PIPE_OPS)
    }

    /// The same count for the Task 1 arm, where every reference recomputes.
    pub fn baseline_mul_pipe_ops(&self) -> u64 {
        u64::from(self.baseline)
            * u64::from(UNISKIP_TAPS as u32)
            * u64::from(DOT_MUL_PIPE_OPS + TAP_ADDRESS_MUL_PIPE_OPS)
    }
}

impl fmt::Display for CachePlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bf = self.slots.iter().filter(|s| s.width == 1).count();
        let e4 = self.slots.len() - bf;
        let fill = self.fill_mul_pipe_ops();
        let uncached = self.uncached_mul_pipe_ops();
        let baseline = self.baseline_mul_pipe_ops();
        writeln!(
            f,
            "  pool                {} B = {} units of {} B",
            UNISKIP_CACHE_POOL_WORDS * size_of::<u32>(),
            UNISKIP_CACHE_UNITS,
            UNISKIP_CACHE_UNIT_BYTES
        )?;
        writeln!(
            f,
            "  cached sources      {} ({bf} bf / {e4} e4), {} of {} units",
            self.slots.len(),
            self.units_used,
            UNISKIP_CACHE_UNITS
        )?;
        writeln!(f, "  C  cached width     {}", self.cached_width)?;
        writeln!(f, "  Ru uncached refs    {}", self.uncached_refs)?;
        writeln!(
            f,
            "  C + Ru              {} (uncached baseline {}, {:.3}x)",
            self.resolver_dots(),
            self.baseline,
            self.resolver_ratio()
        )?;
        writeln!(
            f,
            "  mul-pipe ops / row  fill {fill} + uncached {uncached} = {} (baseline {baseline}, {:.3}x)",
            fill + uncached,
            (fill + uncached) as f64 / baseline.max(1) as f64
        )?;
        write!(
            f,
            "  slots               {:?}",
            self.slots
                .iter()
                .map(|s| (s.unit, s.source, s.refs, s.width))
                .collect::<Vec<_>>()
        )
    }
}

/// Rank the sources and assign the top ones to fixed units.
///
/// The key is **net saving per shared-memory byte**: caching source `s` removes
/// `(refs - 1) * width` of the `refs * width` dots it would otherwise cost (the fill
/// keeps one production per cell) and costs `width * UNISKIP_CACHE_UNIT_BYTES`. The
/// width therefore cancels, so the GLOBAL ranking is `refs - 1` descending with the
/// classes interleaved — `cpu_cache_plan_ranking_is_width_free_across_classes` pins
/// that against the width-weighted key, on a census where the two differ in the
/// cached set and not only in its order. Ties break on the source id, so the plan is
/// deterministic. A source referenced once saves nothing and is never cached.
pub fn plan(program: &SynthProgram) -> CachePlan {
    let refs = &program.census.per_source_refs;
    let width: Vec<u32> = program
        .sources
        .iter()
        .map(|r| component_width(r.source_class))
        .collect();

    let mut ranked: Vec<usize> = (0..program.sources.len())
        .filter(|&id| refs[id] >= 2)
        .collect();
    ranked.sort_by(|&a, &b| {
        // saving_a / bytes_a  vs  saving_b / bytes_b, cross-multiplied in exact u64.
        let saving = |id: usize| u64::from(refs[id] - 1) * u64::from(width[id]);
        let bytes = |id: usize| u64::from(width[id]) * UNISKIP_CACHE_UNIT_BYTES as u64;
        (saving(b) * bytes(a))
            .cmp(&(saving(a) * bytes(b)))
            .then(a.cmp(&b))
    });

    let mut slots = Vec::new();
    let mut source_slot = vec![UNISKIP_CACHE_SLOT_NONE; program.sources.len()];
    let mut fill = [UNISKIP_CACHE_FILL_NONE; UNISKIP_CACHE_UNITS];
    let mut units_used = 0u32;
    for id in ranked {
        let w = width[id];
        if units_used + w > UNISKIP_CACHE_UNITS as u32 {
            continue;
        }
        let unit = units_used as u8;
        for limb in 0..w {
            fill[(units_used + limb) as usize] = id as u16 | ((limb as u16) << 8);
        }
        source_slot[id] = unit;
        slots.push(CacheSlot {
            source: id as u16,
            unit,
            width: w,
            refs: refs[id],
        });
        units_used += w;
    }

    let cached_width = slots.iter().map(|s| s.width).sum();
    let baseline: u32 = (0..program.sources.len())
        .map(|id| refs[id] * width[id])
        .sum();
    let uncached_refs = (0..program.sources.len())
        .filter(|&id| source_slot[id] == UNISKIP_CACHE_SLOT_NONE)
        .map(|id| refs[id] * width[id])
        .sum();

    CachePlan {
        slots,
        source_slot,
        fill,
        units_used,
        cached_width,
        uncached_refs,
        baseline,
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::synth::{generate, Census, TermOrder};

    fn default_program() -> SynthProgram {
        generate(0, Census::default()).unwrap()
    }

    #[test]
    fn cpu_cache_plan_fits_and_is_consistent() {
        let program = default_program();
        let plan = plan(&program);

        assert!(plan.units_used <= UNISKIP_CACHE_UNITS as u32);
        assert_eq!(plan.units_used, plan.cached_width);

        // Every unit of a slab is claimed exactly once, limbs in order, and no free
        // unit sits inside one.
        let mut covered = [false; UNISKIP_CACHE_UNITS];
        for slot in &plan.slots {
            assert_eq!(plan.source_slot[slot.source as usize], slot.unit);
            assert_eq!(
                slot.width,
                component_width(program.sources[slot.source as usize].source_class)
            );
            for limb in 0..slot.width {
                let unit = slot.unit as usize + limb as usize;
                assert!(!covered[unit], "unit {unit} assigned twice");
                covered[unit] = true;
                assert_eq!(plan.fill[unit], slot.source | ((limb as u16) << 8));
            }
        }
        for (unit, &entry) in plan.fill.iter().enumerate() {
            assert_eq!(covered[unit], entry != UNISKIP_CACHE_FILL_NONE);
        }
        assert_eq!(
            covered.iter().filter(|&&c| c).count() as u32,
            plan.units_used
        );

        // C + Ru partitions the reference census exactly: every source is either
        // cached (contributing its width once) or uncached (contributing refs*width).
        let cached_refs: u32 = plan.slots.iter().map(|s| s.refs * s.width).sum();
        assert_eq!(cached_refs + plan.uncached_refs, plan.baseline);
        assert_eq!(plan.baseline, 326);
        assert!(
            plan.resolver_dots() < plan.baseline,
            "the plan must save work"
        );

        // Op-split formula: fill + uncached, against the all-recompute baseline.
        assert_eq!(DOT_MUL_PIPE_OPS, 28);
        assert_eq!(
            plan.baseline_mul_pipe_ops(),
            u64::from(plan.baseline) * 16 * 44
        );
        assert_eq!(
            plan.fill_mul_pipe_ops(),
            u64::from(plan.cached_width) * (16 * 28 + 16)
        );
        assert!(
            plan.fill_mul_pipe_ops() + plan.uncached_mul_pipe_ops() < plan.baseline_mul_pipe_ops()
        );
    }

    #[test]
    fn cpu_cache_plan_ranking() {
        let program = default_program();
        let plan = plan(&program);
        let refs = &program.census.per_source_refs;

        // Never cache a source that saves nothing, and never leave a strictly better
        // candidate out while a worse one is in unless it simply did not fit.
        for slot in &plan.slots {
            assert!(slot.refs >= 2, "source {} saves nothing", slot.source);
        }
        let worst_cached = plan.slots.iter().map(|s| s.refs).min().unwrap();
        for (id, &r) in refs.iter().enumerate() {
            if plan.source_slot[id] != UNISKIP_CACHE_SLOT_NONE {
                continue;
            }
            let width = component_width(program.sources[id].source_class);
            // An excluded source either ranks no better than the worst cached one, or
            // is a wide slab that did not fit in the remaining units.
            assert!(
                r <= worst_cached || plan.units_used + width > UNISKIP_CACHE_UNITS as u32,
                "source {id} ({r} refs) was skipped over a {worst_cached}-ref slab"
            );
        }

        // Within each field class the assignment is exactly `refs - 1` descending,
        // which is what the per-byte cross-class key collapses to (the slab bytes are
        // proportional to the width the saving is proportional to).
        for class in [UNISKIP_SRC_BF_GLOBAL, UNISKIP_SRC_E4_GLOBAL] {
            let mut of_class: Vec<usize> = (0..program.sources.len())
                .filter(|&id| program.sources[id].source_class == class)
                .collect();
            of_class.sort_by_key(|&id| (std::cmp::Reverse(refs[id]), id));
            let cached: Vec<usize> = of_class
                .iter()
                .copied()
                .filter(|&id| plan.source_slot[id] != UNISKIP_CACHE_SLOT_NONE)
                .collect();
            let prefix: Vec<usize> = of_class.into_iter().take(cached.len()).collect();
            assert_eq!(cached, prefix, "class {class} is not a top-K prefix");
        }
    }

    /// The shipped fit loop with a substituted ranking score, so a test can run the
    /// same greedy under a deliberately wrong key.
    fn greedy_scored(program: &SynthProgram, score: impl Fn(usize) -> u64) -> Vec<u16> {
        let refs = &program.census.per_source_refs;
        let mut ranked: Vec<usize> = (0..program.sources.len())
            .filter(|&id| refs[id] >= 2)
            .collect();
        ranked.sort_by(|&a, &b| score(b).cmp(&score(a)).then(a.cmp(&b)));
        let mut used = 0u32;
        let mut out = Vec::new();
        for id in ranked {
            let w = component_width(program.sources[id].source_class);
            if used + w > UNISKIP_CACHE_UNITS as u32 {
                continue;
            }
            used += w;
            out.push(id as u16);
        }
        out
    }

    /// `C + Ru` for an arbitrary cached set — the objective the greedy minimizes.
    fn resolver_dots_of(program: &SynthProgram, cached: &[u16]) -> u32 {
        let refs = &program.census.per_source_refs;
        (0..program.sources.len())
            .map(|id| {
                let w = component_width(program.sources[id].source_class);
                if cached.contains(&(id as u16)) {
                    w
                } else {
                    refs[id] * w
                }
            })
            .sum()
    }

    fn assert_cross_class_ranking(
        program: &SynthProgram,
        expect_shipped: &[u16],
        expect_width_weighted: &[u16],
    ) {
        let plan = plan(program);
        let refs = &program.census.per_source_refs;
        let width = |id: usize| u64::from(component_width(program.sources[id].source_class));

        let shipped: Vec<u16> = plan.slots.iter().map(|s| s.source).collect();
        let by_density = greedy_scored(program, |id| u64::from(refs[id] - 1));
        let width_weighted = greedy_scored(program, |id| u64::from(refs[id] - 1) * width(id));

        assert_eq!(shipped, expect_shipped);
        assert_eq!(width_weighted, expect_width_weighted);
        // The GLOBAL order is `refs - 1` descending, classes ignored — not merely a
        // top-K prefix within each class.
        assert_eq!(
            shipped, by_density,
            "global order is not `refs - 1` descending"
        );
        // …and that is a claim with content: the width-weighted key, which is what
        // forgetting to divide by the slab bytes produces, is a different plan and
        // never a better one on the plan's own objective.
        assert_ne!(shipped, width_weighted);
        assert!(
            resolver_dots_of(program, &shipped) <= resolver_dots_of(program, &width_weighted),
            "width-weighted plan is better: {} vs {}",
            resolver_dots_of(program, &shipped),
            resolver_dots_of(program, &width_weighted)
        );
        // Both classes are in the cached set, so the order above really does cross the
        // bf/e4 boundary.
        let classes: Vec<u8> = shipped
            .iter()
            .map(|&s| program.sources[s as usize].source_class)
            .collect();
        assert!(
            classes.contains(&UNISKIP_SRC_BF_GLOBAL) && classes.contains(&UNISKIP_SRC_E4_GLOBAL)
        );
    }

    #[test]
    fn cpu_cache_plan_ranking_is_width_free_across_classes() {
        // Default census: the two keys agree on the cached SET and disagree on the
        // ORDER — width-weighting hoists the two e4 slabs (refs 7, saving 6 * 4 = 24)
        // ahead of the bf slabs with refs 13 (saving 12) that dominate per byte.
        assert_cross_class_ranking(
            &default_program(),
            &[0, 1, 2, 3, 4, 5, 48, 49, 6, 7],
            &[48, 49, 0, 1, 2, 3, 4, 5, 6, 7],
        );

        // An e4-heavier census, where the two keys disagree on the SET: width-weighting
        // spends the whole 16-unit pool on four e4 slabs (refs 7, 7, 5, 5) and caches
        // nothing else, dropping every refs-13 bf source.
        let e4_heavy = generate(
            0,
            Census {
                sources: 34,
                semantic_terms: 150,
                groups: 25,
                grouped_atoms: 72,
            },
        )
        .unwrap();
        assert_cross_class_ranking(
            &e4_heavy,
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 28, 9, 10, 11],
            &[28, 29, 30, 31],
        );
        // There the two plans are not permutations of one another, so the density key
        // is STRICTLY the better one on `C + Ru` and not merely a tidier order.
        assert!(
            resolver_dots_of(&e4_heavy, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 28, 9, 10, 11])
                < resolver_dots_of(&e4_heavy, &[28, 29, 30, 31])
        );
    }

    #[test]
    fn cpu_cache_plan_is_deterministic_and_order_invariant() {
        let a = plan(&generate(7, Census::default()).unwrap());
        let b = plan(&generate(7, Census::default()).unwrap());
        assert_eq!(a, b);

        // The reference census is a property of the record multiset, so reordering the
        // program must not move a single slot.
        let mut reordered = generate(7, Census::default()).unwrap();
        reordered.apply_term_order(TermOrder::Locality);
        assert_eq!(plan(&reordered), a);
    }

    #[test]
    fn cpu_cache_plan_scales_off_default() {
        // A census small enough that every source fits, and one wide enough that the
        // greedy has to stop.
        let small = Census {
            sources: 34,
            semantic_terms: 90,
            groups: 12,
            grouped_atoms: 36,
        };
        let p = plan(&generate(3, small).unwrap());
        assert!(p.units_used <= UNISKIP_CACHE_UNITS as u32);
        assert!(p.resolver_dots() <= p.baseline);
    }
}
