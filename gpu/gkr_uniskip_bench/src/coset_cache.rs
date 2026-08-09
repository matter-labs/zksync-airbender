//! The v3 R4 coset cache: plan-time admission, slot assignment, and per-arm wire state.
//!
//! SEMANTICS. An admitted source's produced coset pair is written once per thread by a
//! prologue and read back on every later reference; `h` is still loaded at each
//! reference, exactly as in R3. Admission is SOURCE-GLOBAL, so a `PRODUCT`'s two operands
//! each carry their own disposition on their own source record — R3's two-operand tag
//! problem cannot recur.
//!
//! Three orders are kept distinct and must not be conflated:
//!   1. ADMISSION — refs descending, cut at refs >= 2, ties E4 before BF then lower id.
//!   2. SLOT ASSIGNMENT — all E4 spans first, then BF units, so every E4 span is 16-byte
//!      aligned with no padding.
//!   3. PROLOGUE PRODUCTION — E4 list then BF list, within a class in admission order.
//!
//! Arm state is CLONED. The canonical source array (and every R3 path) is never mutated;
//! an arm owns its own copy with `cache_slot` written, so all arms are resident at once.

use crate::abi::*;
use crate::synth::SynthProgram;

// The layout constants live in `abi` beside the wire structs they describe; the frame is
// sized once at the default census's `all-59` footprint so every cached arm compiles to
// ONE body with ONE frame. A program needing more is a plan-time rejection, not a silent
// truncation. `cache_slot` encodes the BASE alone, so bases stay representable for any
// frame up to 256 units; only `0xff` collides with the sentinel (checked per base).
const _: () = assert!(UNISKIP_COSET_FRAME_UNITS <= 256);

/// Which class the prologue produces FIRST. Purely a table-emission order: the kernel
/// walks whatever the host uploaded, so this knob costs no SASS. Spec 3.3 pins
/// `E4First` as the production order; `BfFirst` is the capacity-arm diagnostic, since
/// whichever class is produced last is the one still warm in L1 at walk entry.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "lower")]
pub enum PrologueOrder {
    #[default]
    E4First,
    BfFirst,
}

impl PrologueOrder {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::E4First => "e4first",
            Self::BfFirst => "bffirst",
        }
    }
}

/// The R4 arms. `Control` runs the uncached body; every other arm runs the cached body
/// and differs only in uploaded state — `Cache0` with an empty admitted set, which prices
/// the fixed lookup/frame/branch machinery the way R3's `wnone` priced the window's.
///
/// `rename_all = "lower"` is load-bearing: clap's default is kebab-case, which would make
/// `allrepeat` and `e4rich` — the spellings [`CacheArm::as_str`] emits and the R4 runner
/// will consume — unparseable.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "lower")]
pub enum CacheArm {
    #[default]
    Control,
    Cache0,
    Hot4,
    Hot16,
    AllRepeat,
    All59,
    E4Rich,
}

impl CacheArm {
    pub const ALL: [Self; 7] = [
        Self::Control,
        Self::Cache0,
        Self::Hot4,
        Self::Hot16,
        Self::AllRepeat,
        Self::All59,
        Self::E4Rich,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Control => "control",
            Self::Cache0 => "cache0",
            Self::Hot4 => "hot4",
            Self::Hot16 => "hot16",
            Self::AllRepeat => "allrepeat",
            Self::All59 => "all59",
            Self::E4Rich => "e4rich",
        }
    }

    /// Whether the arm runs the cached kernel body at all.
    pub fn uses_cache(self) -> bool {
        self != Self::Control
    }
}

/// One entry of an ordered admission list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AdmissionEntry {
    pub source: u16,
    pub refs: u32,
    /// Component width: 1 for `bf`, 4 for `e4`.
    pub width: u32,
}

impl AdmissionEntry {
    pub fn is_e4(self) -> bool {
        self.width == UNISKIP_COSET_E4_UNITS
    }
}

/// One prologue table row: the SEMANTIC source id the resolver consumes plus its base
/// unit. Columns are neither unique nor sufficient, so the table is keyed by source id
/// and the base is cross-checked against the record's `cache_slot`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrologueEntry {
    pub source: u16,
    pub base: u8,
}

/// The exact per-walk quantities the spec's machinery table defines. Every field is
/// derived from the live resolver stream, never from the stored census.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CacheCounts {
    /// Admitted `bf` / `e4` source counts.
    pub b: u32,
    pub e: u32,
    /// Reference sums of the admitted `bf` / `e4` sources (NOT width-weighted).
    pub r_b: u32,
    pub r_e: u32,
    /// Footprint in units: `b + 4e`.
    pub c: u32,
    /// Cached references, width-weighted: `r_b + 4 * r_e`.
    pub rc: u32,
    /// Width-weighted production slots the program runs with no cache at all.
    pub passes_without: u32,
    /// Chain calls with this arm's cache: `c + (passes_without - rc)`.
    pub chains: u32,
    /// `STL` instructions: `b` x `STL.64` plus `2e` x `STL.128`.
    pub store_instrs: u32,
    /// `LDL` instructions: `r_b` x `LDL.64` plus `2 * r_e` x `LDL.128`.
    pub load_instrs: u32,
    /// Production slots the cache removes: `rc - c`.
    pub removals: u32,
    /// Touched cache bytes per thread: `8c`. Distinct from the static frame.
    pub bytes: u32,
}

/// Everything one arm uploads: its own source array and its own prologue table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CacheArmState {
    pub arm: CacheArm,
    /// The canonical source array CLONED with `cache_slot` written; `0xff` elsewhere.
    pub sources: Vec<UniskipSourceRecord>,
    /// Admitted sources in admission order.
    pub admitted: Vec<AdmissionEntry>,
    /// Production order: E4 rows first, then BF rows, each in admission order.
    pub prologue_e4: Vec<PrologueEntry>,
    pub prologue_bf: Vec<PrologueEntry>,
    pub counts: CacheCounts,
}

impl CacheArmState {
    /// Prologue rows in production order — E4 first, then BF (spec-pinned).
    pub fn prologue(&self) -> impl Iterator<Item = PrologueEntry> + '_ {
        self.prologue_e4.iter().chain(&self.prologue_bf).copied()
    }

    /// Prologue rows with the class order chosen at launch.
    pub fn prologue_in(
        &self,
        order: PrologueOrder,
    ) -> Box<dyn Iterator<Item = PrologueEntry> + '_> {
        match order {
            PrologueOrder::E4First => {
                Box::new(self.prologue_e4.iter().chain(&self.prologue_bf).copied())
            }
            PrologueOrder::BfFirst => {
                Box::new(self.prologue_bf.iter().chain(&self.prologue_e4).copied())
            }
        }
    }

    /// The uploaded table. SLOT ASSIGNMENT never moves — only the row order does, which is
    /// the whole of the production-order knob.
    pub fn descriptor(&self, order: PrologueOrder) -> UniskipCacheDesc {
        let mut desc = UniskipCacheDesc {
            count: (self.prologue_e4.len() + self.prologue_bf.len()) as u32,
            e4_count: self.prologue_e4.len() as u32,
            bf_count: self.prologue_bf.len() as u32,
            ..Default::default()
        };
        for (slot, row) in self.prologue_in(order).enumerate() {
            desc.entry[slot] = UniskipPrologueEntry {
                source: row.source,
                base: row.base,
                reserved: 0,
            };
        }
        desc
    }
}

/// Width-weighted production slots of one warp-program walk, counted per resolver
/// invocation — the 326 of the default census.
pub fn weighted_passes(program: &SynthProgram) -> u32 {
    program
        .resolver_operands()
        .iter()
        .map(|op| component_width(program.sources[op.source as usize].source_class))
        .sum()
}

/// Every live source (refs >= 1), ordered by the canonical rule: refs descending, then
/// E4 before BF, then lower source id.
///
/// Ranked off [`SynthProgram::resolver_refs`], recomputed from the program rather than
/// read from `census.per_source_refs`, which goes stale under `force_self_products` or a
/// census override.
pub fn ranked_live(program: &SynthProgram) -> Vec<AdmissionEntry> {
    let refs = program.resolver_refs();
    let mut ranked: Vec<AdmissionEntry> = refs
        .iter()
        .enumerate()
        .filter(|&(_, &count)| count > 0)
        .map(|(id, &count)| AdmissionEntry {
            source: id as u16,
            refs: count,
            width: component_width(program.sources[id].source_class),
        })
        .collect();
    ranked.sort_by(|a, b| {
        b.refs
            .cmp(&a.refs)
            .then(b.width.cmp(&a.width))
            .then(a.source.cmp(&b.source))
    });
    ranked
}

/// The canonical admission list: [`ranked_live`] cut at refs >= 2. Once-used sources are
/// never admitted — a store and a load to save nothing.
pub fn canonical_admission(program: &SynthProgram) -> Vec<AdmissionEntry> {
    ranked_live(program)
        .into_iter()
        .filter(|e| e.refs >= 2)
        .collect()
}

/// The E4-only admitted set: exactly the admitted E4 sources, no BF.
///
/// RR ruling 2026-08-09, superseding the earlier "smallest prefix containing every
/// admitted E4 source": at the default census that prefix was 52 of 55 entries — 96 % of
/// all-repeat's footprint — so the stop-signal's E4 leg could not be told apart from
/// capacity. The E4-only set is C = 44 against all-repeat's 88.
pub fn e4_rich(canonical: &[AdmissionEntry]) -> Vec<AdmissionEntry> {
    canonical.iter().copied().filter(|e| e.is_e4()).collect()
}

/// The admitted set of one arm. `All59` is ALL live sources including refs = 1 — the
/// zero-removal waste diagnostic — and is deliberately NOT a prefix of the cutoff list.
pub fn admitted_for(program: &SynthProgram, arm: CacheArm) -> Vec<AdmissionEntry> {
    if arm == CacheArm::All59 {
        return ranked_live(program);
    }
    let canonical = canonical_admission(program);
    // `E4Rich` is a FILTER of the canonical list, not a prefix of it — the only arm that
    // is. Everything downstream takes a source list, so the selection is the whole change.
    if arm == CacheArm::E4Rich {
        return e4_rich(&canonical);
    }
    let take = match arm {
        CacheArm::Control | CacheArm::Cache0 => 0,
        CacheArm::Hot4 => 4,
        CacheArm::Hot16 => 16,
        CacheArm::AllRepeat => canonical.len(),
        CacheArm::All59 | CacheArm::E4Rich => unreachable!("handled above"),
    };
    canonical.into_iter().take(take).collect()
}

/// Build one arm's state. The program is read, never written: `sources` is a clone.
///
/// SLOT ASSIGNMENT, decoupled from admission: all E4 spans first (4 units each, so every
/// base is a multiple of 4 units = 32 B and both 16 B halves are aligned), then one unit
/// per BF source. ENCODE-SITE BOUND: `cache_slot` encodes the base unit ALONE, so the only
/// unrepresentable base is `0xff` (the uncached sentinel) — a span may legitimately run
/// THROUGH unit 255 (an e4 base at 252 spans 252..256). What bounds the layout is the
/// frame: bases stay representable for any frame up to 256 units, and
/// [`UNISKIP_COSET_FRAME_UNITS`] is statically held under that. At the default census
/// C = 92, far inside. The validator enforces both.
pub fn plan_arm(program: &SynthProgram, arm: CacheArm) -> Result<CacheArmState, String> {
    let admitted = admitted_for(program, arm);
    let mut sources = program.sources.clone();
    for rec in sources.iter_mut() {
        rec.cache_slot = UNISKIP_CACHE_SLOT_NONE;
    }

    let mut prologue_e4 = Vec::new();
    let mut prologue_bf = Vec::new();
    let mut next = 0u32;
    for entry in admitted.iter().filter(|e| e.is_e4()) {
        let base = next;
        next += UNISKIP_COSET_E4_UNITS;
        sources[entry.source as usize].cache_slot = base as u8;
        prologue_e4.push(PrologueEntry {
            source: entry.source,
            base: base as u8,
        });
    }
    for entry in admitted.iter().filter(|e| !e.is_e4()) {
        let base = next;
        next += 1;
        sources[entry.source as usize].cache_slot = base as u8;
        prologue_bf.push(PrologueEntry {
            source: entry.source,
            base: base as u8,
        });
    }

    let counts = count(program, &admitted);
    let state = CacheArmState {
        arm,
        sources,
        admitted,
        prologue_e4,
        prologue_bf,
        counts,
    };
    // ALWAYS-ON, not a debug_assert: an invalid plan is a wrong measurement, and R3's
    // lesson is that the host is where that must be caught. FALLIBLE, not a panic: a
    // census can push an arm past the frame (`--sources 60` already does), and an arm
    // nobody selected must not kill a run — least of all a control or R3 run.
    validate(program, &state).map_err(|e| format!("arm {} is not plannable: {e}", arm.as_str()))?;
    Ok(state)
}

/// Every arm's state, each independently fallible. Nothing is uploaded or re-planned
/// inside a timed rotation, and one unplannable arm does not take the others with it.
pub fn plan_all(program: &SynthProgram) -> Vec<(CacheArm, Result<CacheArmState, String>)> {
    CacheArm::ALL
        .iter()
        .map(|&arm| (arm, plan_arm(program, arm)))
        .collect()
}

/// The spec's machinery table for an admitted set.
pub fn count(program: &SynthProgram, admitted: &[AdmissionEntry]) -> CacheCounts {
    let mut c = CacheCounts {
        passes_without: weighted_passes(program),
        ..Default::default()
    };
    for e in admitted {
        if e.is_e4() {
            c.e += 1;
            c.r_e += e.refs;
        } else {
            c.b += 1;
            c.r_b += e.refs;
        }
    }
    c.c = c.b + UNISKIP_COSET_E4_UNITS * c.e;
    c.rc = c.r_b + UNISKIP_COSET_E4_UNITS * c.r_e;
    c.chains = c.c
        + c.passes_without
            .checked_sub(c.rc)
            .expect("cached references exceed the program's production slots");
    c.store_instrs = c.b + 2 * c.e;
    c.load_instrs = c.r_b + 2 * c.r_e;
    c.removals =
        c.rc.checked_sub(c.c)
            .expect("footprint exceeds the cached references it serves");
    c.bytes = UNISKIP_COSET_UNIT_BYTES as u32 * c.c;
    c
}

/// ALWAYS-ON plan-time validation. Rejects anything the device could not execute or
/// would execute wrongly: a misaligned or overlapping span, a span past the frame or past
/// the representable base, a sentinel base, a prologue row whose base disagrees with the
/// source record, and any record marked cached that no prologue row produces.
pub fn validate(program: &SynthProgram, state: &CacheArmState) -> Result<(), String> {
    if state.sources.len() != program.sources.len() {
        return Err(format!(
            "arm {} has {} source records, program has {}",
            state.arm.as_str(),
            state.sources.len(),
            program.sources.len()
        ));
    }

    // The frame is a flat unit array; `occupied[u]` names the source owning unit `u`.
    let mut occupied: Vec<Option<u16>> = vec![None; UNISKIP_COSET_FRAME_UNITS as usize];
    let mut seen = vec![false; program.sources.len()];

    for entry in state.prologue() {
        let id = entry.source as usize;
        if id >= program.sources.len() {
            return Err(format!("prologue row names source {id}, out of range"));
        }
        if seen[id] {
            return Err(format!("source {id} appears twice in the prologue table"));
        }
        seen[id] = true;

        if entry.base == UNISKIP_CACHE_SLOT_NONE {
            return Err(format!("source {id} has the uncached sentinel as its base"));
        }
        let width = component_width(program.sources[id].source_class);
        let base = entry.base as u32;
        if width == UNISKIP_COSET_E4_UNITS
            && !(base as usize * UNISKIP_COSET_UNIT_BYTES).is_multiple_of(UNISKIP_COSET_E4_ALIGN)
        {
            return Err(format!(
                "source {id}: e4 span at unit {base} is not {}-byte aligned",
                UNISKIP_COSET_E4_ALIGN
            ));
        }
        if base + width > UNISKIP_COSET_FRAME_UNITS {
            return Err(format!(
                "source {id}: span {base}..{} exceeds the {UNISKIP_COSET_FRAME_UNITS}-unit frame",
                base + width
            ));
        }
        for unit in base..base + width {
            if let Some(other) = occupied[unit as usize] {
                return Err(format!(
                    "source {id}: unit {unit} already held by source {other}"
                ));
            }
            occupied[unit as usize] = Some(entry.source);
        }
        if state.sources[id].cache_slot != entry.base {
            return Err(format!(
                "source {id}: prologue base {} disagrees with record cache_slot {}",
                entry.base, state.sources[id].cache_slot
            ));
        }
    }

    for (id, rec) in state.sources.iter().enumerate() {
        let cached = rec.cache_slot != UNISKIP_CACHE_SLOT_NONE;
        if cached != seen[id] {
            return Err(format!(
                "source {id}: cache_slot {} but {} in the prologue table",
                rec.cache_slot,
                if seen[id] { "present" } else { "absent" }
            ));
        }
        // Everything else on the record must be the canonical wire, untouched.
        let canonical = program.sources[id];
        if rec.addr != canonical.addr || rec.source_class != canonical.source_class {
            return Err(format!(
                "source {id}: the clone altered more than cache_slot"
            ));
        }
    }

    let expect = count(program, &state.admitted);
    if expect != state.counts {
        return Err(format!(
            "arm {}: recorded counts {:?} disagree with the admitted set {:?}",
            state.arm.as_str(),
            state.counts,
            expect
        ));
    }
    Ok(())
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::synth::{generate, Census, TermOrder};

    fn program(order: TermOrder) -> SynthProgram {
        let mut p = generate(0, Census::default()).unwrap();
        p.apply_term_order(order);
        p
    }

    /// The literals of `.agents/sdd/2026-08-09-v3-r4/expected-counts.md`, which the
    /// controller derived independently of this module. Fields: B, E, R_B, R_E, C, Rc,
    /// chains, stores, loads, removals, bytes.
    const EXPECTED: [(CacheArm, [u32; 11]); 5] = [
        (CacheArm::Hot4, [4, 0, 51, 0, 4, 51, 279, 4, 51, 47, 32]),
        (
            CacheArm::Hot16,
            [12, 4, 93, 20, 28, 173, 181, 20, 133, 145, 224],
        ),
        (
            CacheArm::AllRepeat,
            [44, 11, 186, 34, 88, 322, 92, 66, 254, 234, 704],
        ),
        (
            CacheArm::All59,
            [48, 11, 190, 34, 92, 326, 92, 70, 258, 234, 736],
        ),
        (
            CacheArm::E4Rich,
            [0, 11, 0, 34, 44, 136, 234, 22, 68, 92, 352],
        ),
    ];

    fn actual(c: CacheCounts) -> [u32; 11] {
        [
            c.b,
            c.e,
            c.r_b,
            c.r_e,
            c.c,
            c.rc,
            c.chains,
            c.store_instrs,
            c.load_instrs,
            c.removals,
            c.bytes,
        ]
    }

    #[test]
    fn cpu_cache_default_census_shape() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            let live = ranked_live(&p);
            let bf = live.iter().filter(|e| !e.is_e4()).count();
            let e4 = live.iter().filter(|e| e.is_e4()).count();
            assert_eq!((bf, e4), (48, 11), "live sources, {order:?}");
            assert_eq!(live.len(), 59, "{order:?}");
            assert_eq!(weighted_passes(&p), 326, "{order:?}");

            let canonical = canonical_admission(&p);
            let cbf = canonical.iter().filter(|e| !e.is_e4()).count();
            let ce4 = canonical.iter().filter(|e| e.is_e4()).count();
            assert_eq!((cbf, ce4), (44, 11), "reused sources, {order:?}");
            assert_eq!(canonical.len(), 55, "{order:?}");
            let e4_only = e4_rich(&canonical);
            assert_eq!(e4_only.len(), 11, "e4-rich set, {order:?}");
            assert!(e4_only.iter().all(|e| e.is_e4()), "{order:?}");
        }
    }

    /// The head pins the tie-break: E4 ids 50/51 at refs = 3 precede BF id 6 at refs = 3.
    #[test]
    fn cpu_cache_admission_head_matches_the_artifact() {
        let head: [(u16, u32, u32); 12] = [
            (0, 13, 1),
            (1, 13, 1),
            (2, 13, 1),
            (3, 12, 1),
            (4, 12, 1),
            (5, 12, 1),
            (48, 7, 4),
            (49, 7, 4),
            (50, 3, 4),
            (51, 3, 4),
            (6, 3, 1),
            (7, 3, 1),
        ];
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            let canonical = canonical_admission(&p);
            for (i, &(source, refs, width)) in head.iter().enumerate() {
                assert_eq!(
                    canonical[i],
                    AdmissionEntry {
                        source,
                        refs,
                        width
                    },
                    "admission[{i}], {order:?}"
                );
            }
        }
    }

    #[test]
    fn cpu_cache_counts_match_the_expected_literals() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            for (arm, want) in EXPECTED {
                let state = plan_arm(&p, arm).unwrap();
                assert_eq!(
                    actual(state.counts),
                    want,
                    "arm {} under {order:?}",
                    arm.as_str()
                );
            }
        }
    }

    /// hot-4 is R3's window arm exactly: same four sources, same 13/13/13/12, same 47.
    #[test]
    fn cpu_cache_hot4_mirrors_the_r3_window() {
        let p = program(TermOrder::Locality);
        let state = plan_arm(&p, CacheArm::Hot4).unwrap();
        let sources: Vec<u16> = state.admitted.iter().map(|e| e.source).collect();
        let refs: Vec<u32> = state.admitted.iter().map(|e| e.refs).collect();
        assert_eq!(sources, vec![0, 1, 2, 3]);
        assert_eq!(refs, vec![13, 13, 13, 12]);
        assert_eq!(state.counts.removals, 47);
        assert_eq!(state.counts.chains, 279);
    }

    /// all-59 buys nothing over all-repeat: +4 stores, +4 loads, +32 B, zero removals.
    #[test]
    fn cpu_cache_all59_is_pure_waste_over_all_repeat() {
        let p = program(TermOrder::Locality);
        let repeat = plan_arm(&p, CacheArm::AllRepeat).unwrap().counts;
        let all = plan_arm(&p, CacheArm::All59).unwrap().counts;
        assert_eq!(all.removals, repeat.removals);
        assert_eq!(all.chains, repeat.chains);
        assert_eq!(all.store_instrs - repeat.store_instrs, 4);
        assert_eq!(all.load_instrs - repeat.load_instrs, 4);
        assert_eq!(all.bytes - repeat.bytes, 32);
    }

    /// C_max is the frame constant, and all-59 is what sizes it.
    #[test]
    fn cpu_cache_frame_is_sized_by_all59() {
        let p = program(TermOrder::Locality);
        assert_eq!(
            plan_arm(&p, CacheArm::All59).unwrap().counts.c,
            UNISKIP_COSET_FRAME_UNITS
        );
        assert_eq!(
            UNISKIP_COSET_FRAME_UNITS as usize * UNISKIP_COSET_UNIT_BYTES,
            736
        );
    }

    /// The uploaded table mirrors `native/uniskip_abi.cuh`; drift there is silent
    /// corruption, so the layout and the row contents are both pinned.
    #[test]
    fn cpu_cache_descriptor_layout_and_rows() {
        assert_eq!(size_of::<UniskipPrologueEntry>(), 4);
        assert_eq!(align_of::<UniskipPrologueEntry>(), 4);
        assert_eq!(align_of::<UniskipCacheDesc>(), 16);
        assert_eq!(
            size_of::<UniskipCacheDesc>(),
            4 * UNISKIP_COSET_FRAME_UNITS as usize + 16
        );
        assert_eq!(UNISKIP_COSET_UNIT_BYTES, 8);
        assert_eq!(UNISKIP_COSET_E4_UNITS, 4);
        assert_eq!(UNISKIP_COSET_E4_ALIGN, 16);
        assert_eq!(UNISKIP_COSET_FRAME_UNITS, 92);

        let p = program(TermOrder::Locality);
        let state = plan_arm(&p, CacheArm::AllRepeat).unwrap();
        let e4 = state.descriptor(PrologueOrder::E4First);
        let bf = state.descriptor(PrologueOrder::BfFirst);
        assert_eq!((e4.count, e4.e4_count, e4.bf_count), (55, 11, 44));
        assert_eq!((bf.count, bf.e4_count, bf.bf_count), (55, 11, 44));

        // Only the ROW ORDER moves; slot assignment is identical, which is the whole of
        // the production-order knob.
        let base_of = |d: &UniskipCacheDesc| {
            let mut v: Vec<(u16, u8)> = d.entry[..d.count as usize]
                .iter()
                .map(|e| (e.source, e.base))
                .collect();
            v.sort();
            v
        };
        assert_eq!(base_of(&e4), base_of(&bf));
        assert_eq!(e4.entry[0].source, state.prologue_e4[0].source);
        assert_eq!(bf.entry[0].source, state.prologue_bf[0].source);
        for e in &e4.entry[..e4.count as usize] {
            assert_ne!(e.base, UNISKIP_CACHE_SLOT_NONE);
            assert_eq!(e.reserved, 0);
        }
        // Unused rows stay zeroed, and cache0 uploads an empty table.
        let empty = plan_arm(&p, CacheArm::Cache0)
            .unwrap()
            .descriptor(PrologueOrder::E4First);
        assert_eq!((empty.count, empty.e4_count, empty.bf_count), (0, 0, 0));
    }

    #[test]
    fn cpu_cache_control_and_cache0_admit_nothing() {
        let p = program(TermOrder::Locality);
        for arm in [CacheArm::Control, CacheArm::Cache0] {
            let state = plan_arm(&p, arm).unwrap();
            assert!(state.admitted.is_empty());
            assert_eq!(state.counts.c, 0);
            assert_eq!(state.counts.removals, 0);
            assert_eq!(state.counts.chains, 326);
            assert!(state
                .sources
                .iter()
                .all(|r| r.cache_slot == UNISKIP_CACHE_SLOT_NONE));
        }
    }

    /// Slot assignment is decoupled from admission: E4 spans occupy the low units in
    /// admission order, then BF units, and the prologue is E4-first.
    #[test]
    fn cpu_cache_slots_are_e4_first_and_aligned() {
        let p = program(TermOrder::Locality);
        let state = plan_arm(&p, CacheArm::AllRepeat).unwrap();
        assert_eq!(state.prologue_e4.len(), 11);
        assert_eq!(state.prologue_bf.len(), 44);
        for (i, row) in state.prologue_e4.iter().enumerate() {
            assert_eq!(row.base as u32, UNISKIP_COSET_E4_UNITS * i as u32);
            assert_eq!(
                (row.base as usize * UNISKIP_COSET_UNIT_BYTES) % UNISKIP_COSET_E4_ALIGN,
                0
            );
        }
        for (i, row) in state.prologue_bf.iter().enumerate() {
            assert_eq!(row.base as u32, 44 + i as u32);
        }
        // Production order is E4 then BF, each in admission order.
        let order: Vec<u16> = state.prologue().map(|r| r.source).collect();
        let admitted_e4: Vec<u16> = state
            .admitted
            .iter()
            .filter(|e| e.is_e4())
            .map(|e| e.source)
            .collect();
        assert_eq!(&order[..11], &admitted_e4[..]);
    }

    /// The canonical arrays are never mutated, and every arm is resident at once.
    #[test]
    fn cpu_cache_arm_state_is_cloned_not_mutated() {
        let p = program(TermOrder::Locality);
        let before = p.sources.clone();
        let all = plan_all(&p);
        assert_eq!(p.sources, before, "planning mutated the canonical array");
        assert_eq!(all.len(), CacheArm::ALL.len());
        let cached: Vec<usize> = all
            .iter()
            .map(|(_, s)| {
                s.as_ref()
                    .unwrap()
                    .sources
                    .iter()
                    .filter(|r| r.cache_slot != UNISKIP_CACHE_SLOT_NONE)
                    .count()
            })
            .collect();
        assert_eq!(cached, vec![0, 0, 4, 16, 55, 59, 11]);
        for (_, state) in &all {
            validate(&p, state.as_ref().unwrap()).unwrap();
        }
    }

    /// Refs are recomputed from the live stream, so the stored census going stale under
    /// `force_self_products` cannot leak into admission.
    #[test]
    fn cpu_cache_self_products_recompute_refs() {
        let mut p = program(TermOrder::Locality);
        let before = plan_arm(&p, CacheArm::AllRepeat).unwrap().counts;
        let rewritten = p.force_self_products(12);
        assert_eq!(rewritten, 12);
        let after = plan_arm(&p, CacheArm::AllRepeat).unwrap().counts;
        assert_ne!(
            before, after,
            "admission ignored the rewritten resolver stream"
        );
        assert_eq!(after.passes_without, weighted_passes(&p));
        // The stale stored census would still claim the pre-rewrite refs.
        let live = ranked_live(&p);
        for e in &live {
            assert_eq!(e.refs, p.resolver_refs()[e.source as usize]);
        }
        validate(&p, &plan_arm(&p, CacheArm::AllRepeat).unwrap()).unwrap();
    }

    /// A census can push an arm past the frame. That must fail THAT ARM and nothing
    /// else: control and every R3 lane share this program and never touch the cache.
    #[test]
    fn cpu_cache_over_frame_census_fails_only_the_offending_arms() {
        let census = Census {
            sources: 60,
            ..Census::default()
        };
        let mut p = generate(0, census).unwrap();
        p.apply_term_order(TermOrder::Locality);
        let planned = plan_all(&p);
        let by_arm = |arm: CacheArm| {
            planned
                .iter()
                .find(|(a, _)| *a == arm)
                .map(|(_, s)| s)
                .unwrap()
        };
        assert!(
            plan_arm(&p, CacheArm::All59).unwrap_err().contains("frame"),
            "all59 must be rejected past the frame at --sources 60"
        );
        // The arms a control or R3 run relies on are unaffected.
        for arm in [CacheArm::Control, CacheArm::Cache0, CacheArm::Hot4] {
            by_arm(arm)
                .as_ref()
                .unwrap_or_else(|e| panic!("{} must stay plannable: {e}", arm.as_str()));
        }
        // And the R3 window path over the same program is untouched.
        crate::window::validate(&p, &crate::window::plan(&p)).unwrap();
    }

    #[test]
    fn cpu_cache_degenerate_census_is_planned_not_panicked() {
        let census = Census {
            sources: 9,
            semantic_terms: 12,
            groups: 1,
            grouped_atoms: 3,
        };
        let mut p = generate(0, census).unwrap();
        p.apply_term_order(TermOrder::Locality);
        let live = ranked_live(&p);
        for arm in CacheArm::ALL {
            let state = plan_arm(&p, arm).unwrap();
            validate(&p, &state).unwrap();
            assert!(state.admitted.len() <= live.len());
            // The identity the counts must satisfy at any admitted set.
            let c = state.counts;
            assert_eq!(c.chains, c.c + (c.passes_without - c.rc));
            assert_eq!(c.removals, c.rc - c.c);
        }
    }

    fn corrupt(p: &SynthProgram, arm: CacheArm) -> CacheArmState {
        plan_arm(p, arm).unwrap()
    }

    #[test]
    fn cpu_cache_validator_rejects_overlapping_spans() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::AllRepeat);
        // Point the second E4 span at the first one's units.
        let victim = s.prologue_e4[1].source as usize;
        s.prologue_e4[1].base = 0;
        s.sources[victim].cache_slot = 0;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("already held by source"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_misaligned_e4_span() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::AllRepeat);
        let victim = s.prologue_e4[0].source as usize;
        s.prologue_e4[0].base = 1;
        s.sources[victim].cache_slot = 1;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("not 16-byte aligned"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_span_past_the_frame() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::AllRepeat);
        let victim = s.prologue_bf[0].source as usize;
        s.prologue_bf[0].base = UNISKIP_COSET_FRAME_UNITS as u8;
        s.sources[victim].cache_slot = UNISKIP_COSET_FRAME_UNITS as u8;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("exceeds the"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_sentinel_base() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::AllRepeat);
        let victim = s.prologue_bf[0].source as usize;
        s.prologue_bf[0].base = UNISKIP_CACHE_SLOT_NONE;
        s.sources[victim].cache_slot = UNISKIP_CACHE_SLOT_NONE;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("uncached sentinel"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_base_record_disagreement() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::AllRepeat);
        let victim = s.prologue_bf[0].source as usize;
        s.sources[victim].cache_slot += 1;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("disagrees with record cache_slot"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_cached_record_with_no_prologue_row() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::Hot4);
        let orphan = s
            .sources
            .iter()
            .position(|r| r.cache_slot == UNISKIP_CACHE_SLOT_NONE)
            .unwrap();
        s.sources[orphan].cache_slot = 90;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("absent"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_altered_wire_fields() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::Hot4);
        s.sources[0].addr ^= 1;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("altered more than cache_slot"), "{err}");
    }

    #[test]
    fn cpu_cache_validator_rejects_stale_counts() {
        let p = program(TermOrder::Locality);
        let mut s = corrupt(&p, CacheArm::Hot4);
        s.counts.removals += 1;
        let err = validate(&p, &s).unwrap_err();
        assert!(err.contains("disagree with the admitted set"), "{err}");
    }
}
