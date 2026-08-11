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

/// The R4 arms plus the R5 frontier's `kN` prefix points. `Control` runs the uncached
/// body; every other arm runs the cached body and differs only in uploaded state —
/// `Cache0` with an empty admitted set, which prices the fixed lookup/frame/branch
/// machinery the way R3's `wnone` priced the window's.
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
    E4Top2,
    K24,
    K32,
    K40,
    K45,
    K46,
    K48,
    K49,
    K50,
    K51,
}

impl CacheArm {
    pub const ALL: [Self; 17] = [
        Self::Control,
        Self::Cache0,
        Self::Hot4,
        Self::Hot16,
        Self::AllRepeat,
        Self::All59,
        Self::E4Rich,
        Self::E4Top2,
        Self::K24,
        Self::K32,
        Self::K40,
        Self::K45,
        Self::K46,
        Self::K48,
        Self::K49,
        Self::K50,
        Self::K51,
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
            Self::E4Top2 => "e4top2",
            Self::K24 => "k24",
            Self::K32 => "k32",
            Self::K40 => "k40",
            Self::K45 => "k45",
            Self::K46 => "k46",
            Self::K48 => "k48",
            Self::K49 => "k49",
            Self::K50 => "k50",
            Self::K51 => "k51",
        }
    }

    /// Whether the arm runs the cached kernel body at all.
    pub fn uses_cache(self) -> bool {
        self != Self::Control
    }

    /// The canonical-list prefix length this arm admits, when the arm IS a prefix point.
    /// `AllRepeat` is the whole list at whatever length the census gives it and the three
    /// diagnostics are not prefixes at all, so both answer `None`.
    pub fn prefix_k(self) -> Option<usize> {
        Some(match self {
            Self::Control | Self::Cache0 => 0,
            Self::Hot4 => 4,
            Self::Hot16 => 16,
            Self::K24 => 24,
            Self::K32 => 32,
            Self::K40 => 40,
            Self::K45 => 45,
            Self::K46 => 46,
            Self::K48 => 48,
            Self::K49 => 49,
            Self::K50 => 50,
            Self::K51 => 51,
            Self::AllRepeat | Self::All59 | Self::E4Rich | Self::E4Top2 => return None,
        })
    }
}

/// What a planned state IS: a named arm, or the canonical prefix at a K no enum variant
/// names. `Cache0` is not a neutral stand-in for the second — it names an EMPTY admitted
/// set, so a `plan_prefix(_, 7)` labelled `cache0` describes a plan that admits nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanId {
    Arm(CacheArm),
    Prefix(usize),
}

impl PlanId {
    /// The named arm, or `None` at an unnamed prefix point.
    pub fn arm(self) -> Option<CacheArm> {
        match self {
            Self::Arm(arm) => Some(arm),
            Self::Prefix(_) => None,
        }
    }
}

impl std::fmt::Display for PlanId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arm(arm) => f.pad(arm.as_str()),
            Self::Prefix(k) => f.pad(&format!("prefix{k}")),
        }
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

/// TEST-ONLY corruption of a planned arm, uploaded UNCHECKED — the always-on validator
/// would reject these, which is the point: they prove the device reads the record's
/// `cache_slot` rather than deriving a base.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
#[clap(rename_all = "lower")]
pub enum CacheMutation {
    /// Point one cached reference at a different LIVE slot of the SAME width, so the
    /// device reads real, wrong cosets. Same-width keeps the access forms identical, so a
    /// divergence cannot be blamed on a malformed load.
    Retarget,
}

/// Apply a mutation to an arm's CLONED record array. Returns what it did, or `None` when
/// the arm has too few same-width slots for the mutation to mean anything.
pub fn mutate(state: &mut CacheArmState, how: CacheMutation) -> Option<String> {
    match how {
        CacheMutation::Retarget => {
            let rows: Vec<PrologueEntry> = state.prologue().collect();
            for (i, row) in rows.iter().enumerate() {
                let width = state
                    .admitted
                    .iter()
                    .find(|e| e.source == row.source)
                    .map(|e| e.width)?;
                if let Some(other) = rows.iter().skip(i + 1).find(|o| {
                    state
                        .admitted
                        .iter()
                        .any(|e| e.source == o.source && e.width == width)
                }) {
                    state.sources[row.source as usize].cache_slot = other.base;
                    return Some(format!(
                        "source {} retargeted from unit {} to unit {} (source {}, same width {width})",
                        row.source, row.base, other.base, other.source
                    ));
                }
            }
            None
        }
    }
}

/// Everything one arm uploads: its own source array and its own prologue table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CacheArmState {
    /// What this plan IS. A LABEL: it reaches error strings and the config dump, never the
    /// plan. Lane identity in a factorial comes from the [`CacheLane`], never from here.
    pub id: PlanId,
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

/// The family-stop lane (RR ruling 2026-08-09): the two highest-ref admitted E4 sources in
/// canonical order. `e4rich` stays as the coverage diagnostic; this is the arm that can
/// separate E4 VALUE from capacity, because at 8 units it is nowhere near the frame.
pub fn e4_top2(canonical: &[AdmissionEntry]) -> Vec<AdmissionEntry> {
    e4_rich(canonical).into_iter().take(2).collect()
}

/// The canonical prefix-K set: [`canonical_admission`] truncated at `k`. THE one
/// truncation — every prefix arm and [`plan_prefix`] route through here, so a named arm
/// and its K can never describe different sets, and there is no second ordering to drift.
pub fn prefix_admission(program: &SynthProgram, k: usize) -> Vec<AdmissionEntry> {
    let mut admitted = canonical_admission(program);
    admitted.truncate(k);
    admitted
}

/// The admitted set of one arm. `All59` is ALL live sources including refs = 1 — the
/// zero-removal waste diagnostic — and is deliberately NOT a prefix of the cutoff list;
/// `E4Rich` and `E4Top2` are FILTERS of the canonical list rather than prefixes of it.
///
/// EXHAUSTIVE by construction: a new arm must state which family it joins here rather
/// than inheriting `allrepeat`'s whole list from a wildcard.
pub fn admitted_for(program: &SynthProgram, arm: CacheArm) -> Vec<AdmissionEntry> {
    match arm {
        CacheArm::All59 => ranked_live(program),
        CacheArm::E4Rich => e4_rich(&canonical_admission(program)),
        CacheArm::E4Top2 => e4_top2(&canonical_admission(program)),
        CacheArm::AllRepeat => canonical_admission(program),
        CacheArm::Control
        | CacheArm::Cache0
        | CacheArm::Hot4
        | CacheArm::Hot16
        | CacheArm::K24
        | CacheArm::K32
        | CacheArm::K40
        | CacheArm::K45
        | CacheArm::K46
        | CacheArm::K48
        | CacheArm::K49
        | CacheArm::K50
        | CacheArm::K51 => prefix_admission(
            program,
            arm.prefix_k().expect("every arm in this leg is a prefix"),
        ),
    }
}

/// Build one arm's state. The program is read, never written: `sources` is a clone.
pub fn plan_arm(program: &SynthProgram, arm: CacheArm) -> Result<CacheArmState, String> {
    plan_admitted(program, PlanId::Arm(arm), admitted_for(program, arm))
}

/// The canonical prefix-K plan, defined at every K rather than only at the nine the enum
/// names. `hot16` IS `plan_prefix(_, 16)`: one list, one truncation, one planner.
pub fn plan_prefix(program: &SynthProgram, k: usize) -> Result<CacheArmState, String> {
    plan_admitted(program, prefix_id(k), prefix_admission(program, k))
}

/// What a prefix point IS. LABEL ONLY — it reaches error strings and the config dump,
/// never the plan. A K a cached arm names reports as that arm (K = 0 is `cache0`); a K no
/// arm names reports as itself, since `cache0` would claim an empty admitted set.
fn prefix_id(k: usize) -> PlanId {
    CacheArm::ALL
        .into_iter()
        .find(|a| a.uses_cache() && a.prefix_k() == Some(k))
        .map_or(PlanId::Prefix(k), PlanId::Arm)
}

/// SLOT ASSIGNMENT, decoupled from admission: all E4 spans first (4 units each, so every
/// base is a multiple of 4 units = 32 B and both 16 B halves are aligned), then one unit
/// per BF source. ENCODE-SITE BOUND: `cache_slot` encodes the base unit ALONE, so the only
/// unrepresentable base is `0xff` (the uncached sentinel) — a span may legitimately run
/// THROUGH unit 255 (an e4 base at 252 spans 252..256). What bounds the layout is the
/// frame: bases stay representable for any frame up to 256 units, and
/// [`UNISKIP_COSET_FRAME_UNITS`] is statically held under that. At the default census
/// C = 92, far inside. The validator enforces both.
fn plan_admitted(
    program: &SynthProgram,
    id: PlanId,
    admitted: Vec<AdmissionEntry>,
) -> Result<CacheArmState, String> {
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
        id,
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
    validate(program, &state).map_err(|e| format!("arm {id} is not plannable: {e}"))?;
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
            state.id,
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
            state.id, state.counts, expect
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
    const EXPECTED: [(CacheArm, [u32; 11]); 6] = [
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
        (CacheArm::E4Top2, [0, 2, 0, 14, 8, 56, 278, 4, 28, 48, 64]),
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
            let top2 = e4_top2(&canonical);
            assert_eq!(
                top2.iter().map(|e| (e.source, e.refs)).collect::<Vec<_>>(),
                vec![(48, 7), (49, 7)],
                "e4-top2 family-stop lane, {order:?}"
            );
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

    /// The literals of `.agents/sdd/2026-08-10-v3-r5/expected-counts-r5.md`, controller-
    /// derived independently of this module by the R4 out-of-tree method. Fields in the
    /// artifact's own column order: K, B, E, C, Rc, R_B, R_E, chains, stores, loads,
    /// removals, touched B/thread. `hot16` rides along because the artifact's claim that it
    /// IS the K16 prefix point is one of the things being reproduced.
    #[rustfmt::skip]
    const EXPECTED_R5: [(CacheArm, [u32; 12]); 10] = [
        (CacheArm::Hot16, [16, 12,  4, 28, 173,  93, 20, 181, 20, 133, 145, 224]),
        (CacheArm::K24,   [24, 20,  4, 36, 197, 117, 20, 165, 28, 157, 161, 288]),
        (CacheArm::K32,   [32, 28,  4, 44, 221, 141, 20, 149, 36, 181, 177, 352]),
        (CacheArm::K40,   [40, 36,  4, 52, 245, 165, 20, 133, 44, 205, 193, 416]),
        (CacheArm::K45,   [45, 41,  4, 57, 260, 180, 20, 123, 49, 220, 203, 456]),
        (CacheArm::K46,   [46, 41,  5, 61, 268, 180, 22, 119, 51, 224, 207, 488]),
        (CacheArm::K48,   [48, 41,  7, 69, 284, 180, 26, 111, 55, 232, 215, 552]),
        (CacheArm::K49,   [49, 41,  8, 73, 292, 180, 28, 107, 57, 236, 219, 584]),
        (CacheArm::K50,   [50, 41,  9, 77, 300, 180, 30, 103, 59, 240, 223, 616]),
        (CacheArm::K51,   [51, 41, 10, 81, 308, 180, 32,  99, 61, 244, 227, 648]),
    ];

    /// The FULL 55-entry ordering printed on `oracle-derivation.txt`'s
    /// `admission head (id,refs,w)` line, identical under both term orders. Every lane's
    /// admitted-id list is a PREFIX of this, in this order: counts alone cannot detect a
    /// reversal among equal-ref, equal-class sources, which is what this pins.
    #[rustfmt::skip]
    const ADMISSION_ORDER: [(u16, u32, u32); 55] = [
        (0, 13, 1), (1, 13, 1), (2, 13, 1), (3, 12, 1), (4, 12, 1), (5, 12, 1),
        (48, 7, 4), (49, 7, 4), (50, 3, 4), (51, 3, 4),
        (6, 3, 1), (7, 3, 1), (8, 3, 1), (9, 3, 1), (10, 3, 1), (11, 3, 1), (12, 3, 1),
        (13, 3, 1), (14, 3, 1), (15, 3, 1), (16, 3, 1), (17, 3, 1), (18, 3, 1), (19, 3, 1),
        (20, 3, 1), (21, 3, 1), (22, 3, 1), (23, 3, 1), (24, 3, 1), (25, 3, 1), (26, 3, 1),
        (27, 3, 1), (28, 3, 1), (29, 3, 1), (30, 3, 1), (31, 3, 1), (32, 3, 1), (33, 3, 1),
        (34, 3, 1), (35, 3, 1), (36, 3, 1), (37, 3, 1), (38, 3, 1), (39, 3, 1), (40, 3, 1),
        (52, 2, 4), (53, 2, 4), (54, 2, 4), (55, 2, 4), (56, 2, 4), (57, 2, 4), (58, 2, 4),
        (41, 2, 1), (42, 2, 1), (43, 2, 1),
    ];

    fn actual_r5(state: &CacheArmState) -> [u32; 12] {
        let c = state.counts;
        [
            state.admitted.len() as u32,
            c.b,
            c.e,
            c.c,
            c.rc,
            c.r_b,
            c.r_e,
            c.chains,
            c.store_instrs,
            c.load_instrs,
            c.removals,
            c.bytes,
        ]
    }

    /// All twelve oracle fields, every frontier lane, both orders — the artifact's claim
    /// that the frontier is identical under census and locality included.
    #[test]
    fn cpu_frontier_counts_match_the_r5_oracle() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            for (arm, want) in EXPECTED_R5 {
                let state = plan_arm(&p, arm).unwrap();
                assert_eq!(
                    actual_r5(&state),
                    want,
                    "arm {} under {order:?}",
                    arm.as_str()
                );
                assert!(
                    state.counts.c <= UNISKIP_COSET_FRAME_UNITS,
                    "arm {} needs {} units of the {UNISKIP_COSET_FRAME_UNITS}-unit frame",
                    arm.as_str(),
                    state.counts.c
                );
            }
        }
    }

    #[test]
    fn cpu_frontier_admission_order_matches_the_oracle() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            let got: Vec<(u16, u32, u32)> = canonical_admission(&p)
                .iter()
                .map(|e| (e.source, e.refs, e.width))
                .collect();
            assert_eq!(got, ADMISSION_ORDER.to_vec(), "{order:?}");
        }
    }

    /// The reversal gate: the admitted-id LIST, order-sensitive, against the oracle's
    /// first-K prefix. A swap of two equal-ref, equal-class entries leaves every count
    /// identical and only this test sees it.
    #[test]
    fn cpu_frontier_admitted_ids_are_the_oracle_prefixes() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            for (arm, want) in EXPECTED_R5 {
                let k = want[0] as usize;
                let got: Vec<u16> = plan_arm(&p, arm)
                    .unwrap()
                    .admitted
                    .iter()
                    .map(|e| e.source)
                    .collect();
                let expect: Vec<u16> = ADMISSION_ORDER[..k].iter().map(|&(id, ..)| id).collect();
                assert_eq!(got, expect, "arm {} under {order:?}", arm.as_str());
            }
        }
    }

    /// The spelling clap parses and the spelling a log line carries are one string. They
    /// come from two different mechanisms — `rename_all = "lower"` and [`CacheArm::as_str`]
    /// — so nothing but this keeps `--cache-arm k48` and an ARM line's `k48` in agreement.
    #[test]
    fn cpu_cache_arm_clap_spellings_match_as_str() {
        use clap::ValueEnum;
        for arm in CacheArm::ALL {
            assert_eq!(
                arm.to_possible_value().unwrap().get_name(),
                arm.as_str(),
                "{arm:?}"
            );
        }
        assert_eq!(CacheArm::value_variants().len(), CacheArm::ALL.len());
    }

    /// hot16 IS the K16 prefix point — the WHOLE plan, not merely the counts. The frontier
    /// is truncations of one list, so a second admission ordering cannot exist to drift.
    #[test]
    fn cpu_frontier_prefix16_is_hot16() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            assert_eq!(
                plan_prefix(&p, 16).unwrap(),
                plan_arm(&p, CacheArm::Hot16).unwrap(),
                "{order:?}"
            );
        }
        // Every named prefix arm, likewise, at its own K. `control` is excluded: it admits
        // nothing but is not a cached arm, so the K = 0 label belongs to `cache0`.
        let p = program(TermOrder::Locality);
        for arm in CacheArm::ALL.into_iter().filter(|a| a.uses_cache()) {
            let Some(k) = arm.prefix_k() else { continue };
            assert_eq!(
                plan_prefix(&p, k).unwrap(),
                plan_arm(&p, arm).unwrap(),
                "{}",
                arm.as_str()
            );
        }
        // A K past the list is the list, and allrepeat is that point by another name.
        assert_eq!(
            plan_prefix(&p, canonical_admission(&p).len())
                .unwrap()
                .admitted,
            plan_arm(&p, CacheArm::AllRepeat).unwrap().admitted
        );
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

        // REFACTOR GUARD, not evidence of a live invariant: `PrologueOrder` never reaches
        // `plan_arm`, so slot assignment cannot depend on it today. This fails if someone
        // later threads the order into planning, which is exactly the mistake to catch.
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
        assert_eq!(
            cached,
            vec![0, 0, 4, 16, 55, 59, 11, 2, 24, 32, 40, 45, 46, 48, 49, 50, 51]
        );
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

#[cfg(test)]
mod mixed_operand_probe {
    use super::*;
    use crate::abi::*;
    use crate::synth::{generate, Census, TermOrder};

    /// The R3 two-operand lesson's direct guard: PRODUCT records whose two operands have
    /// DIFFERENT cache dispositions. Source-global admission is supposed to make these
    /// trivially correct, and this is what names the cells the device gate checks.
    #[test]
    fn cpu_cache_mixed_operand_products_exist() {
        let mut p = generate(0, Census::default()).unwrap();
        p.apply_term_order(TermOrder::Locality);
        for arm in [CacheArm::Hot4, CacheArm::E4Top2, CacheArm::Hot16] {
            let state = plan_arm(&p, arm).unwrap();
            let cached = |id: u16| state.sources[id as usize].cache_slot != UNISKIP_CACHE_SLOT_NONE;
            let (mut a_only, mut b_only, mut selfp) = (vec![], vec![], vec![]);
            for (pc, t) in p.program.iter().enumerate() {
                let is_product = matches!(
                    t.term_class,
                    UNISKIP_CLASS_PRODUCT_BF_BF
                        | UNISKIP_CLASS_PRODUCT_BF_E4
                        | UNISKIP_CLASS_PRODUCT_E4_E4
                );
                if !is_product {
                    continue;
                }
                if t.source_a == t.source_b {
                    if cached(t.source_a) {
                        selfp.push(pc);
                    }
                    continue;
                }
                match (cached(t.source_a), cached(t.source_b)) {
                    (true, false) => a_only.push(pc),
                    (false, true) => b_only.push(pc),
                    _ => {}
                }
            }
            println!(
                "arm {}: A-cached/B-not {:?}; B-cached/A-not {:?}; cached self-product {:?}",
                arm.as_str(),
                &a_only[..a_only.len().min(4)],
                &b_only[..b_only.len().min(4)],
                &selfp[..selfp.len().min(4)]
            );
            assert!(
                !a_only.is_empty() && !b_only.is_empty(),
                "arm {} has no mixed-operand product to gate",
                arm.as_str()
            );
        }
    }

    /// The self-product cell CANNOT be observed on the default census — it emits none, so
    /// the probe above always reports an empty list and asserting on it would be vacuous.
    /// `force_self_products` is the only way to reach it, and the admitted set has to
    /// actually COVER the rewritten sources or the cell is still not exercised.
    ///
    /// The knob VALUE decides which classes are reached. `force_self_products` rewrites
    /// both `PRODUCT_BF_BF` and `PRODUCT_E4_E4` (`is_binary_product`), but it rewrites the
    /// first `count` in program order, and in locality order the 6 E4xE4 records sit after
    /// the 54 BF ones — so 12 reaches BF only and 60, the exact maximum, reaches all of
    /// them. Without this, `resolve_second`'s cache-path short-circuit would be gated on
    /// BF alone.
    #[test]
    fn cpu_cache_cached_self_products_cover_both_classes() {
        let mut p = generate(0, Census::default()).unwrap();
        p.apply_term_order(TermOrder::Locality);
        assert_eq!(p.force_self_products(60), 60, "60 is the program's maximum");
        let e4_self = p
            .program
            .iter()
            .filter(|t| t.term_class == UNISKIP_CLASS_PRODUCT_E4_E4 && t.source_a == t.source_b)
            .count();
        assert_eq!(
            e4_self, 6,
            "all six E4xE4 records must be self-products at 60"
        );
        let mut e4_covered = vec![];
        for arm in [
            CacheArm::Hot4,
            CacheArm::Hot16,
            CacheArm::E4Top2,
            CacheArm::E4Rich,
            CacheArm::AllRepeat,
        ] {
            let state = plan_arm(&p, arm).unwrap();
            let hit = p.program.iter().any(|t| {
                t.term_class == UNISKIP_CLASS_PRODUCT_E4_E4
                    && t.source_a == t.source_b
                    && state.sources[t.source_a as usize].cache_slot != UNISKIP_CACHE_SLOT_NONE
            });
            if hit {
                e4_covered.push(arm.as_str());
            }
        }
        // MEASURED, not transcribed: `hot16` covers one too, because it admits the four
        // top-ref E4 sources and one of the six E4xE4 self-products lands on them. The
        // review's expected set named the three E4-heavy arms only.
        assert_eq!(
            e4_covered,
            vec!["hot16", "e4top2", "e4rich", "allrepeat"],
            "E4 cache-path self-product coverage at --self-products 60"
        );
    }

    /// The same cell at the matrix's default knob value, which reaches BF only.
    #[test]
    fn cpu_cache_cached_self_products_are_reachable() {
        let mut p = generate(0, Census::default()).unwrap();
        p.apply_term_order(TermOrder::Locality);
        assert_eq!(p.force_self_products(12), 12);
        let mut covered = 0;
        for arm in [
            CacheArm::Hot4,
            CacheArm::Hot16,
            CacheArm::E4Top2,
            CacheArm::E4Rich,
            CacheArm::AllRepeat,
        ] {
            let state = plan_arm(&p, arm).unwrap();
            let cached = |id: u16| state.sources[id as usize].cache_slot != UNISKIP_CACHE_SLOT_NONE;
            let mut selfp = vec![];
            for (pc, t) in p.program.iter().enumerate() {
                let is_product = matches!(
                    t.term_class,
                    UNISKIP_CLASS_PRODUCT_BF_BF
                        | UNISKIP_CLASS_PRODUCT_BF_E4
                        | UNISKIP_CLASS_PRODUCT_E4_E4
                );
                if is_product && t.source_a == t.source_b && cached(t.source_a) {
                    selfp.push((pc, t.source_a));
                }
            }
            println!(
                "arm {} under force_self_products(12): cached self-products {:?}",
                arm.as_str(),
                &selfp[..selfp.len().min(6)]
            );
            covered += usize::from(!selfp.is_empty());
        }
        assert!(
            covered > 0,
            "no arm reaches a CACHED self-product even under force_self_products — the \
             resolve_second short-circuit is untested on the cache path"
        );
    }
}

/// One lane of the v3 R4 primary factorial: a (block size, arm, launch-bounds) triple that
/// names exactly one kernel. Eleven of them, and the exclusions are enforced by
/// construction rather than by convention — `all59`, `e4rich`, `e4top2`, the BF-first
/// prologue order and the unbounded cached-128 body are 3B diagnostics that run as separate
/// same-session single-arm runs, never inside the rotation.
/// Where a lane's produced coset pairs live. `Local` is the R4/R5/R6 per-thread frame —
/// every pre-R7 lane — and the five seg values are the R7 block-wide carriers, each naming
/// exactly one kernel, one sticky carveout percent and one supported arm set.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum LaneCarrier {
    /// Not reachable from the CLI: the absence of `--carrier` IS this value.
    #[default]
    #[clap(skip)]
    Local,
    #[clap(name = "seg-s")]
    SegS64,
    #[clap(name = "seg-s100")]
    SegS100,
    #[clap(name = "seg-s-acc")]
    SegSAcc,
    #[clap(name = "seg-g")]
    SegG,
    #[clap(name = "seg-recompute")]
    SegRecompute,
}

impl LaneCarrier {
    /// The segmented carriers, in the order their hints are applied and echoed.
    pub const SEG: [Self; 5] = [
        Self::SegS64,
        Self::SegS100,
        Self::SegSAcc,
        Self::SegG,
        Self::SegRecompute,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::SegS64 => "seg-s",
            Self::SegS100 => "seg-s100",
            Self::SegSAcc => "seg-s-acc",
            Self::SegG => "seg-g",
            Self::SegRecompute => "seg-recompute",
        }
    }

    /// The kernel this carrier launches, or `None` for the local frame — whose kernel is
    /// decided by the block size and the launch bound instead.
    pub fn kernel(self) -> Option<LaneKernel> {
        Some(match self {
            Self::Local => return None,
            Self::SegS64 => LaneKernel::SegSCv64,
            Self::SegS100 => LaneKernel::SegSCv100,
            Self::SegSAcc => LaneKernel::SegSAcc,
            Self::SegG => LaneKernel::SegG,
            Self::SegRecompute => LaneKernel::SegRecompute,
        })
    }

    pub fn is_seg(self) -> bool {
        self != Self::Local
    }

    /// The preferred shared-memory carveout this carrier's symbol is set to before any
    /// launch. `_cv64` and `_cv100` are ONE body under two symbols precisely because the
    /// attribute is per-function and sticky; carrier G and the machinery floor take the
    /// winner's 32 KiB configuration, which at a 128-thread kernel is NOT the driver
    /// default (R6 measured that at 64 KiB).
    pub fn carveout(self) -> Option<u32> {
        Some(match self {
            Self::Local => return None,
            Self::SegS64 | Self::SegSAcc => 32,
            Self::SegS100 => 100,
            Self::SegG | Self::SegRecompute => 16,
        })
    }

    /// Whether the slab is device scratch the caller allocates, rather than the launch's
    /// own dynamic shared memory.
    pub fn uses_slab(self) -> bool {
        self == Self::SegG
    }

    /// Whether the body reads the prologue table and the records' `cache_slot` at all. The
    /// machinery floor does not: its carrier points at the reduction plane, so a live slot
    /// would read ~21 KiB past a 2 KiB allocation.
    pub fn uses_plan(self) -> bool {
        self.is_seg() && self != Self::SegRecompute
    }

    /// THE support matrix: which cache arms this carrier is measured with. The lane-set
    /// validator and the `--carrier` surface both read it, so a pair rejected on one is
    /// rejected on the other.
    pub fn supports(self, arm: CacheArm) -> bool {
        match self {
            Self::Local => true,
            Self::SegRecompute => arm == CacheArm::Cache0,
            Self::SegSAcc => arm == CacheArm::Hot16,
            Self::SegS64 => matches!(arm, CacheArm::Cache0 | CacheArm::Hot16),
            Self::SegS100 => matches!(arm, CacheArm::Hot16 | CacheArm::K24 | CacheArm::K40),
            Self::SegG => matches!(
                arm,
                CacheArm::Cache0
                    | CacheArm::Hot16
                    | CacheArm::K24
                    | CacheArm::K40
                    | CacheArm::AllRepeat
            ),
        }
    }

    /// The arms this carrier runs, in `CacheArm::ALL` order — the rejection message's list.
    pub fn supported_arms(self) -> Vec<&'static str> {
        CacheArm::ALL
            .iter()
            .filter(|&&arm| self.supports(arm))
            .map(|arm| arm.as_str())
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CacheLane {
    pub label: &'static str,
    pub block_threads: u32,
    pub arm: CacheArm,
    /// Where this lane's produced coset pairs live. `Local` is every pre-R7 lane.
    pub carrier: LaneCarrier,
    /// Bounded body. At 256 there is no sibling and this is always false; at 128 the
    /// cached arms are bounded (the occupancy gate) and `control128_lb` is the bounded
    /// no-cache baseline that makes the contrast bound-to-bound.
    pub launch_bounds: bool,
    /// Compiled registers and blocks/SM, MEASURED (Task 1A/1B freeze artifacts). They live
    /// here so the emitter reads occupancy off the log instead of carrying constants.
    pub regs: u32,
    pub blocks_per_sm: u32,
}

/// The primary rotation, in a fixed order. 11 arms, so a round count must be a multiple of
/// 11 for every arm to start equally often.
pub const CACHE_FACTORIAL: [CacheLane; 11] = [
    CacheLane {
        label: "control@256",
        block_threads: 256,
        arm: CacheArm::Control,
        carrier: LaneCarrier::Local,
        launch_bounds: false,
        regs: 72,
        blocks_per_sm: 3,
    },
    CacheLane {
        label: "cache0@256",
        block_threads: 256,
        arm: CacheArm::Cache0,
        carrier: LaneCarrier::Local,
        launch_bounds: false,
        regs: 75,
        blocks_per_sm: 3,
    },
    CacheLane {
        label: "hot4@256",
        block_threads: 256,
        arm: CacheArm::Hot4,
        carrier: LaneCarrier::Local,
        launch_bounds: false,
        regs: 75,
        blocks_per_sm: 3,
    },
    CacheLane {
        label: "hot16@256",
        block_threads: 256,
        arm: CacheArm::Hot16,
        carrier: LaneCarrier::Local,
        launch_bounds: false,
        regs: 75,
        blocks_per_sm: 3,
    },
    CacheLane {
        label: "allrepeat@256",
        block_threads: 256,
        arm: CacheArm::AllRepeat,
        carrier: LaneCarrier::Local,
        launch_bounds: false,
        regs: 75,
        blocks_per_sm: 3,
    },
    CacheLane {
        label: "control@128",
        block_threads: 128,
        arm: CacheArm::Control,
        carrier: LaneCarrier::Local,
        launch_bounds: false,
        regs: 72,
        blocks_per_sm: 7,
    },
    CacheLane {
        label: "control_lb@128",
        block_threads: 128,
        arm: CacheArm::Control,
        carrier: LaneCarrier::Local,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    },
    CacheLane {
        label: "cache0@128",
        block_threads: 128,
        arm: CacheArm::Cache0,
        carrier: LaneCarrier::Local,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    },
    CacheLane {
        label: "hot4@128",
        block_threads: 128,
        arm: CacheArm::Hot4,
        carrier: LaneCarrier::Local,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    },
    CacheLane {
        label: "hot16@128",
        block_threads: 128,
        arm: CacheArm::Hot16,
        carrier: LaneCarrier::Local,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    },
    CacheLane {
        label: "allrepeat@128",
        block_threads: 128,
        arm: CacheArm::AllRepeat,
        carrier: LaneCarrier::Local,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    },
];

/// A bounded 128-thread R5 frontier lane. Every one launches the SAME frozen
/// `eval_lsb_pair_cached_128_lb` / `eval_lsb_pair_128_lb` body R4 measured — the kernel is
/// untouched all rung and an arm differs only in uploaded state — so R4's 72 registers /
/// 7 blocks per SM carry over verbatim rather than being a new claim.
const fn frontier_128(label: &'static str, arm: CacheArm) -> CacheLane {
    CacheLane {
        label,
        block_threads: 128,
        arm,
        carrier: LaneCarrier::Local,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    }
}

/// The in-rotation shipping anchor, identical to `CACHE_FACTORIAL`'s first lane.
const FRONTIER_CONTROL_256: CacheLane = CacheLane {
    label: "control@256",
    block_threads: 256,
    arm: CacheArm::Control,
    carrier: LaneCarrier::Local,
    launch_bounds: false,
    regs: 72,
    blocks_per_sm: 3,
};

/// The R5 primary frontier rotation (spec 2.2), in a fixed order: the six canonical
/// prefix points under test, then the incumbent, the machinery arm and the bounded control
/// at 128, then the shipping anchor at 256. 10 lanes, so a round count must be a multiple
/// of 10 for every lane to start equally often.
pub const FRONTIER_FACTORIAL: [CacheLane; 10] = [
    frontier_128("k24@128", CacheArm::K24),
    frontier_128("k32@128", CacheArm::K32),
    frontier_128("k40@128", CacheArm::K40),
    frontier_128("k45@128", CacheArm::K45),
    frontier_128("k46@128", CacheArm::K46),
    frontier_128("k48@128", CacheArm::K48),
    frontier_128("hot16@128", CacheArm::Hot16),
    frontier_128("cache0@128", CacheArm::Cache0),
    frontier_128("control_lb@128", CacheArm::Control),
    FRONTIER_CONTROL_256,
];

/// The conditional extension rotation (spec 2.3): the refs-2 E4 tail past k48, with k48
/// itself riding along so the k48 -> k49 boundary is PAIRED in-session, plus the four
/// anchor lanes both sessions share (k48, hot16, cache0, control_lb, control@256) so a
/// cross-session comparison never has to go raw. 8 lanes => rounds a multiple of 8.
pub const FRONTIER_EXTENSION: [CacheLane; 8] = [
    frontier_128("k48@128", CacheArm::K48),
    frontier_128("k49@128", CacheArm::K49),
    frontier_128("k50@128", CacheArm::K50),
    frontier_128("k51@128", CacheArm::K51),
    frontier_128("hot16@128", CacheArm::Hot16),
    frontier_128("cache0@128", CacheArm::Cache0),
    frontier_128("control_lb@128", CacheArm::Control),
    FRONTIER_CONTROL_256,
];

/// The v3 R6 carveout-probe rotation (spec R6): the three lanes past the R5 knee (`k40`
/// sizes a moved frontier so a `k32` win needs no second probe), the incumbent, and the
/// shipping anchor. The cached lanes all launch the frozen `eval_lsb_pair_cached_128_lb`
/// body, whose carveout the `--carveout-hint` flag steers; `control@256` launches the
/// uncached body and is NEVER hinted — the cross-process anchor. 5 lanes, so a round count
/// must be a multiple of 5.
pub const CARVEOUT_PROBE: [CacheLane; 5] = [
    frontier_128("k24@128", CacheArm::K24),
    frontier_128("k32@128", CacheArm::K32),
    frontier_128("k40@128", CacheArm::K40),
    frontier_128("hot16@128", CacheArm::Hot16),
    FRONTIER_CONTROL_256,
];

/// A v3 R7 segmented lane: 128 threads and bounded like every seg symbol, at the 72
/// registers / 7 blocks per SM Task 3 and Task 4 measured on all five of them.
const fn seg_128(label: &'static str, arm: CacheArm, carrier: LaneCarrier) -> CacheLane {
    CacheLane {
        label,
        block_threads: 128,
        arm,
        carrier,
        launch_bounds: true,
        regs: 72,
        blocks_per_sm: 7,
    }
}

/// The v3 R7 shared-memory-carrier rotation: the three local anchors (the shipping
/// `control@256`, the bounded 128 control and the hinted incumbent), the machinery floor,
/// and the carrier-S points. `seg-hot16-s64` and `seg-hot16-s100` are ONE body under two
/// carveout requests, which is the whole reason two symbols exist. 10 lanes, so a round
/// count must be a multiple of 10.
pub const SEG_SMEM: [CacheLane; 10] = [
    FRONTIER_CONTROL_256,
    frontier_128("control_lb@128", CacheArm::Control),
    frontier_128("hot16@128", CacheArm::Hot16),
    seg_128(
        "seg-recompute@128",
        CacheArm::Cache0,
        LaneCarrier::SegRecompute,
    ),
    seg_128("seg-cache0-s@128", CacheArm::Cache0, LaneCarrier::SegS64),
    seg_128("seg-hot16-s64@128", CacheArm::Hot16, LaneCarrier::SegS64),
    seg_128("seg-hot16-s100@128", CacheArm::Hot16, LaneCarrier::SegS100),
    seg_128("seg-k24-s@128", CacheArm::K24, LaneCarrier::SegS100),
    seg_128("seg-k40-s@128", CacheArm::K40, LaneCarrier::SegS100),
    seg_128("seg-hot16-acc@128", CacheArm::Hot16, LaneCarrier::SegSAcc),
];

/// The v3 R7 device-scratch-carrier rotation: the same three local anchors and machinery
/// floor, then carrier G at four capture points. `allrepeat` rides here and not in
/// [`SEG_SMEM`] because a whole-list slab is far past what a shared partition holds.
/// 9 lanes, so a round count must be a multiple of 9.
pub const SEG_GMEM: [CacheLane; 9] = [
    FRONTIER_CONTROL_256,
    frontier_128("control_lb@128", CacheArm::Control),
    frontier_128("hot16@128", CacheArm::Hot16),
    seg_128(
        "seg-recompute@128",
        CacheArm::Cache0,
        LaneCarrier::SegRecompute,
    ),
    seg_128("seg-cache0-g@128", CacheArm::Cache0, LaneCarrier::SegG),
    seg_128("seg-hot16-g@128", CacheArm::Hot16, LaneCarrier::SegG),
    seg_128("seg-k24-g@128", CacheArm::K24, LaneCarrier::SegG),
    seg_128("seg-k40-g@128", CacheArm::K40, LaneCarrier::SegG),
    seg_128(
        "seg-allrepeat-g@128",
        CacheArm::AllRepeat,
        LaneCarrier::SegG,
    ),
];

/// The v3 R7 anchor rotation: the hinted incumbent against the never-hinted shipping
/// anchor, and nothing else. It carries no seg lane and no dealt program — its two jobs are
/// re-anchoring the seg sessions and pricing the incumbent's carveout hint as a PAIRED
/// per-round contrast, which a standalone log cannot do under session drift. 2 lanes.
pub const SEG_ANCHOR: [CacheLane; 2] = [
    FRONTIER_CONTROL_256,
    frontier_128("hot16@128", CacheArm::Hot16),
];

/// Fail-closed structural check of a pinned lane set — THE one implementation of the
/// factorial pre-flight, called by the runner before it builds anything and by the tests
/// that pin the shipped rotations. Rejects a duplicate label, an unplannable lane, a
/// footprint past the frame, a cached lane that removes nothing (cache0 under another
/// name, which reads as a clean zero effect rather than as a bug), and two lanes of the
/// same kernel admitting the SAME set — R3's aliasing failure shape, where one experiment
/// runs under two labels. `control` and `cache0` admit nothing BY DESIGN, so both of the
/// last two are claims about the lanes that admit something.
pub fn validate_lane_set(program: &SynthProgram, lanes: &[CacheLane]) -> Result<(), String> {
    let mut labels: Vec<&str> = lanes.iter().map(|l| l.label).collect();
    labels.sort_unstable();
    if let Some(dup) = labels.windows(2).find(|w| w[0] == w[1]) {
        return Err(format!("lane label {} appears twice", dup[0]));
    }

    // (admitted ids, block size, bounded, carrier, label) — flat, so the tuple stays
    // readable.
    let mut seen: Vec<(Vec<u16>, u32, bool, LaneCarrier, &str)> = Vec::new();
    for lane in lanes {
        if lane.carrier.is_seg() {
            // Every seg symbol is `__launch_bounds__(128, 7)`: a lane naming another shape
            // would launch a grid the body's row map does not cover.
            if lane.block_threads as usize != UNISKIP_PAIR_THREADS_128 || !lane.launch_bounds {
                return Err(format!(
                    "seg lane {} must be the bounded {UNISKIP_PAIR_THREADS_128}-thread shape",
                    lane.label
                ));
            }
            // THE support matrix, enforced where the set is pinned rather than only at the
            // CLI. `seg-recompute` off `cache0` is the sharp one: its carrier points at the
            // reduction plane, so one live `cache_slot` is a shared read ~21 KiB past a
            // 2 KiB allocation.
            if !lane.carrier.supports(lane.arm) {
                return Err(format!(
                    "seg lane {}: carrier {} runs {}, not {}",
                    lane.label,
                    lane.carrier.as_str(),
                    lane.carrier.supported_arms().join(" | "),
                    lane.arm.as_str()
                ));
            }
        }
        let state = plan_arm(program, lane.arm).map_err(|e| format!("lane {}: {e}", lane.label))?;
        // BELT AND BRACES: unreachable today, because `plan_arm`'s always-on validator
        // rejects an over-frame span first (that is the error the line above carries). It
        // stays because the frame is the lane set's claim as much as the plan's, and a
        // future planner that only warns must not slip a lane past this function.
        if state.counts.c > UNISKIP_COSET_FRAME_UNITS {
            return Err(format!(
                "lane {}: C = {} units exceeds the {UNISKIP_COSET_FRAME_UNITS}-unit frame",
                lane.label, state.counts.c
            ));
        }
        if lane.is_zero_removal_alias(state.counts) {
            return Err(format!(
                "lane {} is a cached arm that removes nothing — it is cache0 under \
                 another name, and the contrast would read as a zero effect",
                lane.label
            ));
        }
        if !lane.arm.uses_cache() || lane.arm == CacheArm::Cache0 {
            continue;
        }
        let ids: Vec<u16> = state.admitted.iter().map(|e| e.source).collect();
        // The key is the whole EXPERIMENT, not the admitted set alone: the same set on the
        // bounded and unbounded bodies is a legitimate contrast (that is what prices the
        // bound), so `launch_bounds` belongs in it or the pair would false-alias. The
        // CARRIER belongs in it for the same reason — one admitted set on two carriers, or
        // on two carveout requests of one carrier, is the R7 contrast itself.
        if let Some((.., other)) = seen.iter().find(|(set, size, bounded, carrier, _)| {
            *set == ids
                && *size == lane.block_threads
                && *bounded == lane.launch_bounds
                && *carrier == lane.carrier
        }) {
            return Err(format!(
                "lanes {} and {other} admit the same set at {} threads",
                lane.label, lane.block_threads
            ));
        }
        seen.push((
            ids,
            lane.block_threads,
            lane.launch_bounds,
            lane.carrier,
            lane.label,
        ));
    }
    Ok(())
}

/// A pinned rotation the runner can execute, with the flag that selects it, the log
/// keyword its lines carry and its preregistered round counts. ONE value names all four,
/// so a mode cannot be paired with another mode's lane set or balance divisor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneSet {
    /// R4's eleven-lane primary rotation (spec R4 2.2). UNTOUCHED by R5.
    CacheFactorial,
    /// R5's ten-lane admission-frontier rotation (spec R5 2.2).
    FrontierFactorial,
    /// R5's conditional eight-lane extension over the refs-2 E4 tail (spec R5 2.3).
    FrontierExtension,
    /// R6's five-lane carveout probe (spec R6): the R5 knee neighborhood re-measured under
    /// a steered shared-memory carveout.
    CarveoutProbe,
    /// R7's ten-lane shared-memory-carrier rotation (spec R7).
    SegSmem,
    /// R7's nine-lane device-scratch-carrier rotation (spec R7).
    SegGmem,
    /// R7's two-lane anchor/attribution rotation (spec R7): local kernels only.
    SegAnchor,
}

impl LaneSet {
    pub fn lanes(self) -> &'static [CacheLane] {
        match self {
            Self::CacheFactorial => &CACHE_FACTORIAL,
            Self::FrontierFactorial => &FRONTIER_FACTORIAL,
            Self::FrontierExtension => &FRONTIER_EXTENSION,
            Self::CarveoutProbe => &CARVEOUT_PROBE,
            Self::SegSmem => &SEG_SMEM,
            Self::SegGmem => &SEG_GMEM,
            Self::SegAnchor => &SEG_ANCHOR,
        }
    }

    /// Whether this rotation runs any segmented lane — the sets that deal the program and
    /// print the `SEG` line. The anchor rotation is local-only and must not.
    pub fn is_seg(self) -> bool {
        self.lanes().iter().any(|lane| lane.carrier.is_seg())
    }

    /// The CLI flag that selects this rotation.
    pub fn flag(self) -> &'static str {
        match self {
            Self::CacheFactorial => "--cache-factorial",
            Self::FrontierFactorial => "--frontier-factorial",
            Self::FrontierExtension => "--frontier-extension",
            Self::CarveoutProbe => "--carveout-probe",
            Self::SegSmem => "--seg-smem-factorial",
            Self::SegGmem => "--seg-gmem-factorial",
            Self::SegAnchor => "--seg-anchor",
        }
    }

    /// The log keyword this rotation's schedule and trailer lines carry. R4's logs keep
    /// R4's word: the emitter keys its lane set, round count and signed threshold off it,
    /// so the two grammars are told apart by the log itself and never by a flag.
    pub fn tag(self) -> &'static str {
        match self {
            Self::CacheFactorial => "CACHE-FACTORIAL",
            Self::FrontierFactorial => "FRONTIER-FACTORIAL",
            Self::FrontierExtension => "FRONTIER-EXTENSION",
            Self::CarveoutProbe => "CARVEOUT-PROBE",
            Self::SegSmem => "SEG-SMEM",
            Self::SegGmem => "SEG-GMEM",
            Self::SegAnchor => "SEG-ANCHOR",
        }
    }

    /// Preregistered `(rounds, warmup)` per term order — spec R5 2.2/2.3, R7 for the seg
    /// sets. 100/10 over ten lanes, 104/16 over eight, 99/9 over the nine gmem lanes; the
    /// warmup is a whole number of rotations in every case. R4's own defaults are not
    /// preregistered here (its record used 110 explicitly).
    pub fn rounds_and_warmup(self) -> Option<(u32, u32)> {
        match self {
            Self::CacheFactorial => None,
            Self::FrontierFactorial => Some((100, 10)),
            Self::FrontierExtension => Some((104, 16)),
            Self::CarveoutProbe => Some((100, 10)),
            Self::SegSmem => Some((100, 10)),
            Self::SegGmem => Some((99, 9)),
            Self::SegAnchor => Some((100, 10)),
        }
    }

    /// Whether the rotation is one of the R5 frontier sets — the ones whose ARM lines
    /// carry the ordered admitted-id list.
    pub fn is_frontier(self) -> bool {
        self != Self::CacheFactorial
    }

    /// What this rotation's lanes ARE, for the wrong-mode rejection.
    pub fn arms_noun(self) -> &'static str {
        match self {
            Self::CacheFactorial => "R4 arms",
            Self::FrontierFactorial | Self::FrontierExtension => "R5 frontier lanes",
            Self::CarveoutProbe => "R6 probe lanes",
            Self::SegSmem | Self::SegGmem => "R7 seg lanes",
            Self::SegAnchor => "R7 anchor lanes",
        }
    }

    /// The gate suite a diagnostic probe belongs in instead of a timing run.
    pub fn gates(self) -> &'static str {
        match self {
            Self::CacheFactorial => "tools/r4_gates.sh",
            Self::FrontierFactorial | Self::FrontierExtension => "tools/r5_gates.sh",
            Self::CarveoutProbe => "tools/r6_gates.sh",
            Self::SegSmem | Self::SegGmem | Self::SegAnchor => "tools/r7_gates.sh",
        }
    }

    /// How the config block names this rotation.
    pub fn noun(self) -> &'static str {
        match self {
            Self::CacheFactorial => "factorial",
            Self::FrontierFactorial => "frontier factorial",
            Self::FrontierExtension => "frontier extension",
            Self::CarveoutProbe => "carveout probe",
            Self::SegSmem => "seg smem factorial",
            Self::SegGmem => "seg gmem factorial",
            Self::SegAnchor => "seg anchor",
        }
    }
}

impl CacheLane {
    /// The kernel this lane launches, by name — the same strings `Harness::eval_kernel`
    /// reports, so a log line and a single-arm config block are comparable.
    pub fn kernel(self) -> LaneKernel {
        // Carrier FIRST: a seg lane names its symbol outright, and the block size / launch
        // bound it also carries are facts about that symbol rather than a second selector.
        if let Some(kernel) = self.carrier.kernel() {
            return kernel;
        }
        match (
            self.block_threads,
            self.arm.uses_cache(),
            self.launch_bounds,
        ) {
            (128, true, true) => LaneKernel::Cached128Lb,
            (128, true, false) => LaneKernel::Cached128,
            (128, false, true) => LaneKernel::Pair128Lb,
            (128, false, false) => LaneKernel::Pair128,
            (_, true, _) => LaneKernel::Cached,
            (_, false, _) => LaneKernel::Pair,
        }
    }

    /// Whether this lane claims a cache but removes nothing — `cache0` under another name,
    /// whose contrast reads as a clean +0.000 rather than as a bug. Structural, so the gate
    /// is exercisable without a census that produces the degenerate plan: none can, because
    /// every prefix cuts at refs >= 2 and so removes at least one production per source.
    pub fn is_zero_removal_alias(self, counts: CacheCounts) -> bool {
        self.arm.uses_cache() && self.arm != CacheArm::Cache0 && counts.removals == 0
    }

    /// Logical rows one block of this lane covers.
    pub fn rows_per_block(self) -> u32 {
        if self.block_threads == 128 {
            UNISKIP_PAIR_ROWS_PER_BLOCK_128 as u32
        } else {
            UNISKIP_PAIR_ROWS_PER_BLOCK as u32
        }
    }
}

/// The kernel a lane runs. SINGLE SOURCE OF TRUTH: the name the log prints and the function
/// the GPU launches both derive from this one value, so they cannot drift apart — two
/// parallel matches is exactly how a log can describe a kernel the run did not use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneKernel {
    Pair,
    Pair128,
    Pair128Lb,
    Cached,
    Cached128,
    Cached128Lb,
    SegSCv64,
    SegSCv100,
    SegSAcc,
    SegG,
    SegRecompute,
}

impl LaneKernel {
    /// The exported symbol minus the `ab_gkr_uniskip_` / `_kernel` affixes — what the ARM
    /// lines, the config block and the carveout echoes all print.
    pub fn name(self) -> &'static str {
        match self {
            Self::Pair => "eval_lsb_pair",
            Self::Pair128 => "eval_lsb_pair_128",
            Self::Pair128Lb => "eval_lsb_pair_128_lb",
            Self::Cached => "eval_lsb_pair_cached",
            Self::Cached128 => "eval_lsb_pair_cached_128",
            Self::Cached128Lb => "eval_lsb_pair_cached_128_lb",
            Self::SegSCv64 => "eval_lsb_seg_s_cv64",
            Self::SegSCv100 => "eval_lsb_seg_s_cv100",
            Self::SegSAcc => "eval_lsb_seg_s_acc",
            Self::SegG => "eval_lsb_seg_g",
            Self::SegRecompute => "eval_lsb_seg_recompute",
        }
    }

    /// Whether the body reads the R4 per-thread coset frame. A seg body reads a block-wide
    /// slab instead, so it is not one of these however its arm is planned.
    pub fn is_cached(self) -> bool {
        matches!(self, Self::Cached | Self::Cached128 | Self::Cached128Lb)
    }
}

#[cfg(test)]
mod lane_tests {
    use super::*;
    use crate::synth::{generate, Census, TermOrder};

    fn program(order: TermOrder) -> SynthProgram {
        let mut p = generate(0, Census::default()).unwrap();
        p.apply_term_order(order);
        p
    }

    /// The R5 rotations' shape, pinned exactly as spec 2.2/2.3 name them. A dropped lane
    /// or a stray arm would otherwise surface only as a changed round count in a timed log.
    #[test]
    fn cpu_frontier_lane_sets() {
        assert_eq!(FRONTIER_FACTORIAL.len(), 10);
        assert_eq!(FRONTIER_EXTENSION.len(), 8);
        let labels = |set: &[CacheLane]| set.iter().map(|l| l.label).collect::<Vec<_>>();
        assert_eq!(
            labels(&FRONTIER_FACTORIAL),
            vec![
                "k24@128",
                "k32@128",
                "k40@128",
                "k45@128",
                "k46@128",
                "k48@128",
                "hot16@128",
                "cache0@128",
                "control_lb@128",
                "control@256",
            ]
        );
        assert_eq!(
            labels(&FRONTIER_EXTENSION),
            vec![
                "k48@128",
                "k49@128",
                "k50@128",
                "k51@128",
                "hot16@128",
                "cache0@128",
                "control_lb@128",
                "control@256",
            ]
        );
        for lane in FRONTIER_FACTORIAL.iter().chain(&FRONTIER_EXTENSION) {
            assert_eq!(lane.regs, 72, "{}", lane.label);
            assert!(
                !matches!(
                    lane.arm,
                    CacheArm::All59
                        | CacheArm::E4Rich
                        | CacheArm::E4Top2
                        | CacheArm::Hot4
                        | CacheArm::AllRepeat
                ),
                "{} is not an R5 frontier arm",
                lane.label
            );
            if lane.block_threads == 128 {
                // The occupancy gate: an unbounded cached lane at 128 would carry a
                // block-count step against the control it is contrasted with.
                assert!(lane.launch_bounds, "{} must be bounded", lane.label);
                assert_eq!(lane.blocks_per_sm, 7, "{}", lane.label);
                assert_eq!(lane.rows_per_block(), 16, "{}", lane.label);
                let want = if lane.arm.uses_cache() {
                    LaneKernel::Cached128Lb
                } else {
                    LaneKernel::Pair128Lb
                };
                assert_eq!(lane.kernel(), want, "{}", lane.label);
            } else {
                assert_eq!(lane.label, "control@256");
                assert_eq!(lane.kernel(), LaneKernel::Pair, "{}", lane.label);
                assert_eq!(lane.rows_per_block(), 32, "{}", lane.label);
                assert_eq!(lane.blocks_per_sm, 3, "{}", lane.label);
            }
        }
        // The lanes both sessions share: the seam a cross-session comparison goes through,
        // so it never has to be taken raw.
        let shared: Vec<&str> = FRONTIER_FACTORIAL
            .iter()
            .map(|l| l.label)
            .filter(|l| FRONTIER_EXTENSION.iter().any(|e| e.label == *l))
            .collect();
        assert_eq!(
            shared,
            vec![
                "k48@128",
                "hot16@128",
                "cache0@128",
                "control_lb@128",
                "control@256"
            ]
        );
    }

    /// The preregistered round and warmup counts divide their rotations, so every lane
    /// occupies every rotation position the same number of times.
    #[test]
    fn cpu_frontier_round_counts_balance() {
        for n in [100u32, 10] {
            assert!(n.is_multiple_of(FRONTIER_FACTORIAL.len() as u32), "{n}");
        }
        for n in [104u32, 16] {
            assert!(n.is_multiple_of(FRONTIER_EXTENSION.len() as u32), "{n}");
        }
        for n in [100u32, 10] {
            assert!(n.is_multiple_of(CARVEOUT_PROBE.len() as u32), "{n}");
        }
        for n in [100u32, 10] {
            assert!(n.is_multiple_of(SEG_SMEM.len() as u32), "{n}");
        }
        for n in [99u32, 9] {
            assert!(n.is_multiple_of(SEG_GMEM.len() as u32), "{n}");
        }
        for n in [100u32, 10] {
            assert!(n.is_multiple_of(SEG_ANCHOR.len() as u32), "{n}");
        }
    }

    /// The R6 probe rotation's shape, pinned exactly as spec R6 names it: the knee
    /// neighborhood on the ONE steerable cached body, the incumbent, and the never-hinted
    /// uncached anchor — nothing else, because a fifth cached lane would stretch the
    /// session and a second anchor would blur the cross-process seam.
    #[test]
    fn cpu_carveout_probe_lane_set() {
        let labels: Vec<&str> = CARVEOUT_PROBE.iter().map(|l| l.label).collect();
        assert_eq!(
            labels,
            vec!["k24@128", "k32@128", "k40@128", "hot16@128", "control@256"]
        );
        assert_eq!(LaneSet::CarveoutProbe.rounds_and_warmup(), Some((100, 10)));
        for lane in &CARVEOUT_PROBE {
            if lane.block_threads == 128 {
                assert!(lane.arm.uses_cache(), "{}", lane.label);
                assert_eq!(lane.kernel(), LaneKernel::Cached128Lb, "{}", lane.label);
            } else {
                assert_eq!(lane.label, "control@256");
                assert_eq!(lane.kernel(), LaneKernel::Pair, "{}", lane.label);
            }
        }
        for order in [TermOrder::Census, TermOrder::Locality] {
            validate_lane_set(&program(order), &CARVEOUT_PROBE).unwrap();
        }
    }

    /// The R7 shared-memory rotation's shape, pinned exactly as the spec names it: three
    /// local anchors, the machinery floor, and the carrier-S points — including the two
    /// `hot16` lanes that differ ONLY in which carveout symbol they launch, which is the
    /// contrast the two symbols exist for.
    #[test]
    fn cpu_seg_smem_lane_set() {
        let labels: Vec<&str> = SEG_SMEM.iter().map(|l| l.label).collect();
        assert_eq!(
            labels,
            vec![
                "control@256",
                "control_lb@128",
                "hot16@128",
                "seg-recompute@128",
                "seg-cache0-s@128",
                "seg-hot16-s64@128",
                "seg-hot16-s100@128",
                "seg-k24-s@128",
                "seg-k40-s@128",
                "seg-hot16-acc@128",
            ]
        );
        assert_eq!(LaneSet::SegSmem.rounds_and_warmup(), Some((100, 10)));
        assert!(LaneSet::SegSmem.is_seg());
        let carriers: Vec<LaneCarrier> = SEG_SMEM.iter().map(|l| l.carrier).collect();
        assert_eq!(
            carriers,
            vec![
                LaneCarrier::Local,
                LaneCarrier::Local,
                LaneCarrier::Local,
                LaneCarrier::SegRecompute,
                LaneCarrier::SegS64,
                LaneCarrier::SegS64,
                LaneCarrier::SegS100,
                LaneCarrier::SegS100,
                LaneCarrier::SegS100,
                LaneCarrier::SegSAcc,
            ]
        );
        let arms: Vec<CacheArm> = SEG_SMEM.iter().map(|l| l.arm).collect();
        assert_eq!(
            arms,
            vec![
                CacheArm::Control,
                CacheArm::Control,
                CacheArm::Hot16,
                CacheArm::Cache0,
                CacheArm::Cache0,
                CacheArm::Hot16,
                CacheArm::Hot16,
                CacheArm::K24,
                CacheArm::K40,
                CacheArm::Hot16,
            ]
        );
        seg_lane_facts(&SEG_SMEM);
    }

    /// The R7 device-scratch rotation, same shape check. `allrepeat` rides HERE and only
    /// here: a whole-list slab is far past what a shared partition holds.
    #[test]
    fn cpu_seg_gmem_lane_set() {
        let labels: Vec<&str> = SEG_GMEM.iter().map(|l| l.label).collect();
        assert_eq!(
            labels,
            vec![
                "control@256",
                "control_lb@128",
                "hot16@128",
                "seg-recompute@128",
                "seg-cache0-g@128",
                "seg-hot16-g@128",
                "seg-k24-g@128",
                "seg-k40-g@128",
                "seg-allrepeat-g@128",
            ]
        );
        assert_eq!(LaneSet::SegGmem.rounds_and_warmup(), Some((99, 9)));
        assert!(LaneSet::SegGmem.is_seg());
        let carriers: Vec<LaneCarrier> = SEG_GMEM.iter().skip(4).map(|l| l.carrier).collect();
        assert_eq!(carriers, vec![LaneCarrier::SegG; 5]);
        assert_eq!(SEG_GMEM[3].carrier, LaneCarrier::SegRecompute);
        assert_eq!(SEG_GMEM[8].arm, CacheArm::AllRepeat);
        seg_lane_facts(&SEG_GMEM);
    }

    /// The R7 anchor rotation carries NO seg lane: it re-anchors the seg sessions and
    /// prices the incumbent's hint as a paired contrast, so a dealt program would be a
    /// second variable — and the emitter rejects an anchor log that carries the SEG line.
    #[test]
    fn cpu_seg_anchor_lane_set() {
        let labels: Vec<&str> = SEG_ANCHOR.iter().map(|l| l.label).collect();
        assert_eq!(labels, vec!["control@256", "hot16@128"]);
        assert_eq!(LaneSet::SegAnchor.rounds_and_warmup(), Some((100, 10)));
        assert!(!LaneSet::SegAnchor.is_seg());
        assert!(SEG_ANCHOR.iter().all(|l| l.carrier == LaneCarrier::Local));
        assert_eq!(SEG_ANCHOR[0].kernel(), LaneKernel::Pair);
        assert_eq!(SEG_ANCHOR[1].kernel(), LaneKernel::Cached128Lb);
    }

    /// The facts every seg lane shares: the bounded 128 shape at Task 3/4's measured
    /// occupancy, the kernel its carrier names, and an arm on that carrier's matrix.
    fn seg_lane_facts(set: &[CacheLane]) {
        for lane in set.iter().filter(|l| l.carrier.is_seg()) {
            assert_eq!(lane.block_threads as usize, UNISKIP_PAIR_THREADS_128);
            assert!(lane.launch_bounds, "{}", lane.label);
            assert_eq!(lane.regs, 72, "{}", lane.label);
            assert_eq!(lane.blocks_per_sm, 7, "{}", lane.label);
            assert_eq!(lane.rows_per_block(), 16, "{}", lane.label);
            assert_eq!(
                lane.kernel(),
                lane.carrier.kernel().unwrap(),
                "{}",
                lane.label
            );
            assert!(lane.carrier.supports(lane.arm), "{}", lane.label);
        }
        // The local anchors keep their pre-R7 dispatch, carrier or not.
        for lane in set.iter().filter(|l| !l.carrier.is_seg()) {
            let want = match (lane.block_threads as usize, lane.arm.uses_cache()) {
                (UNISKIP_PAIR_THREADS_128, true) => LaneKernel::Cached128Lb,
                (UNISKIP_PAIR_THREADS_128, false) => LaneKernel::Pair128Lb,
                _ => LaneKernel::Pair,
            };
            assert_eq!(lane.kernel(), want, "{}", lane.label);
        }
    }

    /// The five seg symbols and their sticky carveout requests, pinned: the names feed the
    /// ARM lines, the config block and the hint echoes, and the percents ARE the carrier
    /// configuration under test (16 -> 32 KiB, 32 -> 64 KiB, 100 -> 100 KiB).
    #[test]
    fn cpu_seg_carrier_kernels_and_carveouts_are_pinned() {
        let named: Vec<(&str, Option<u32>)> = LaneCarrier::SEG
            .iter()
            .map(|&c| (c.kernel().unwrap().name(), c.carveout()))
            .collect();
        assert_eq!(
            named,
            vec![
                ("eval_lsb_seg_s_cv64", Some(32)),
                ("eval_lsb_seg_s_cv100", Some(100)),
                ("eval_lsb_seg_s_acc", Some(32)),
                ("eval_lsb_seg_g", Some(16)),
                ("eval_lsb_seg_recompute", Some(16)),
            ]
        );
        assert_eq!(LaneCarrier::Local.kernel(), None);
        assert_eq!(LaneCarrier::Local.carveout(), None);
        assert_eq!(LaneCarrier::default(), LaneCarrier::Local);
        assert!(LaneCarrier::SegG.uses_slab());
        assert!(LaneCarrier::SEG.iter().all(|c| c.is_seg()));
        assert!(!LaneCarrier::SegS64.uses_slab());
        // The machinery floor takes no plan: its carrier IS the reduction plane.
        assert!(!LaneCarrier::SegRecompute.uses_plan());
        assert!(LaneCarrier::SegS64.uses_plan());
        assert_eq!(
            LaneCarrier::SegG.supported_arms(),
            vec!["cache0", "hot16", "allrepeat", "k24", "k40"]
        );
        assert_eq!(
            LaneCarrier::SegS100.supported_arms(),
            vec!["hot16", "k24", "k40"]
        );
        assert_eq!(LaneCarrier::SegSAcc.supported_arms(), vec!["hot16"]);
    }

    /// The three R7 rotations' preregistered facts, from the ONE value that names them.
    #[test]
    fn cpu_seg_lane_set_selectors() {
        let facts: Vec<(&str, &str, &str, &str, Option<(u32, u32)>)> =
            [LaneSet::SegSmem, LaneSet::SegGmem, LaneSet::SegAnchor]
                .iter()
                .map(|&s| {
                    (
                        s.flag(),
                        s.tag(),
                        s.noun(),
                        s.gates(),
                        s.rounds_and_warmup(),
                    )
                })
                .collect();
        assert_eq!(
            facts,
            vec![
                (
                    "--seg-smem-factorial",
                    "SEG-SMEM",
                    "seg smem factorial",
                    "tools/r7_gates.sh",
                    Some((100, 10))
                ),
                (
                    "--seg-gmem-factorial",
                    "SEG-GMEM",
                    "seg gmem factorial",
                    "tools/r7_gates.sh",
                    Some((99, 9))
                ),
                (
                    "--seg-anchor",
                    "SEG-ANCHOR",
                    "seg anchor",
                    "tools/r7_gates.sh",
                    Some((100, 10))
                ),
            ]
        );
        for set in [LaneSet::SegSmem, LaneSet::SegGmem] {
            assert_eq!(set.arms_noun(), "R7 seg lanes");
        }
        assert_eq!(LaneSet::SegAnchor.arms_noun(), "R7 anchor lanes");
        assert_eq!(LaneSet::SegSmem.lanes(), &SEG_SMEM);
        assert_eq!(LaneSet::SegGmem.lanes(), &SEG_GMEM);
        assert_eq!(LaneSet::SegAnchor.lanes(), &SEG_ANCHOR);
    }

    #[test]
    fn cpu_seg_lane_sets_validate() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            for set in [&SEG_SMEM[..], &SEG_GMEM[..], &SEG_ANCHOR[..]] {
                validate_lane_set(&p, set).unwrap();
            }
        }
    }

    /// The seg validator's teeth. A carrier/arm pair off the pinned matrix is a wrong
    /// measurement at best — `seg-recompute` with a live plan is a shared read past the
    /// reduction plane — and two lanes of ONE carrier admitting one set is R3's aliasing
    /// shape again. The counter-case is the R7 contrast itself: one admitted set on two
    /// carriers must PASS, which is why the alias key carries the carrier.
    #[test]
    fn cpu_seg_lane_set_validator_rejects_off_matrix_pairs() {
        let p = program(TermOrder::Locality);

        let live_recompute = [seg_128(
            "seg-recompute-hot16@128",
            CacheArm::Hot16,
            LaneCarrier::SegRecompute,
        )];
        let err = validate_lane_set(&p, &live_recompute).unwrap_err();
        assert!(
            err.contains("carrier seg-recompute runs cache0, not hot16"),
            "{err}"
        );

        let off_matrix = [seg_128(
            "seg-k24-s64@128",
            CacheArm::K24,
            LaneCarrier::SegS64,
        )];
        let err = validate_lane_set(&p, &off_matrix).unwrap_err();
        assert!(err.contains("carrier seg-s runs cache0 | hot16"), "{err}");

        let unbounded = [CacheLane {
            launch_bounds: false,
            ..seg_128("seg-hot16-s64@128", CacheArm::Hot16, LaneCarrier::SegS64)
        }];
        let err = validate_lane_set(&p, &unbounded).unwrap_err();
        assert!(
            err.contains("must be the bounded 128-thread shape"),
            "{err}"
        );

        let aliased = [
            seg_128("seg-hot16-g@128", CacheArm::Hot16, LaneCarrier::SegG),
            seg_128("seg-hot16-g-again@128", CacheArm::Hot16, LaneCarrier::SegG),
        ];
        let err = validate_lane_set(&p, &aliased).unwrap_err();
        assert!(err.contains("admit the same set"), "{err}");

        let carrier_contrast = [
            seg_128("seg-hot16-s64@128", CacheArm::Hot16, LaneCarrier::SegS64),
            seg_128("seg-hot16-s100@128", CacheArm::Hot16, LaneCarrier::SegS100),
            seg_128("seg-hot16-g@128", CacheArm::Hot16, LaneCarrier::SegG),
            frontier_128("hot16@128", CacheArm::Hot16),
        ];
        validate_lane_set(&p, &carrier_contrast).unwrap();
    }

    #[test]
    fn cpu_frontier_lane_sets_validate() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            for set in [
                &FRONTIER_FACTORIAL[..],
                &FRONTIER_EXTENSION[..],
                &CACHE_FACTORIAL[..],
            ] {
                validate_lane_set(&p, set).unwrap();
                for lane in set {
                    let c = plan_arm(&p, lane.arm).unwrap().counts.c;
                    assert!(
                        c <= UNISKIP_COSET_FRAME_UNITS,
                        "{} needs {c} of {UNISKIP_COSET_FRAME_UNITS} units, {order:?}",
                        lane.label
                    );
                }
            }
        }
    }

    /// The validator's teeth. Two lanes admitting one set is R3's aliasing failure shape —
    /// one experiment under two labels — and a duplicated label is the same bug earlier.
    /// The bounded/unbounded pair is the counter-case: same arm, same block size, DIFFERENT
    /// experiment, so the key carries `launch_bounds` and the pair must pass.
    #[test]
    fn cpu_frontier_lane_set_validator_rejects_aliases_and_duplicates() {
        let p = program(TermOrder::Locality);
        let aliased = [
            frontier_128("k48@128", CacheArm::K48),
            frontier_128("k48-again@128", CacheArm::K48),
        ];
        let err = validate_lane_set(&p, &aliased).unwrap_err();
        assert!(err.contains("admit the same set"), "{err}");

        let duped = [
            frontier_128("k48@128", CacheArm::K48),
            frontier_128("k48@128", CacheArm::K49),
        ];
        let err = validate_lane_set(&p, &duped).unwrap_err();
        assert!(err.contains("appears twice"), "{err}");

        let bound_contrast = [
            frontier_128("k48@128", CacheArm::K48),
            CacheLane {
                launch_bounds: false,
                label: "k48_nolb@128",
                ..frontier_128("k48@128", CacheArm::K48)
            },
        ];
        validate_lane_set(&p, &bound_contrast).unwrap();
    }

    /// A cached lane that removes nothing is `cache0` under another name: its contrast
    /// reads as a clean +0.000 rather than as a bug. No census the generator can build
    /// produces that plan (every prefix cuts at refs >= 2), so the gate's predicate is
    /// exercised directly — and every shipped lane is asserted clear of it.
    #[test]
    fn cpu_lane_zero_removal_alias_is_rejected() {
        let zero = CacheCounts::default();
        let one = CacheCounts {
            removals: 1,
            ..CacheCounts::default()
        };
        let k48 = frontier_128("k48@128", CacheArm::K48);
        assert!(k48.is_zero_removal_alias(zero));
        assert!(!k48.is_zero_removal_alias(one));
        // `cache0` admits nothing BY DESIGN and is exempt; so is the uncached control.
        assert!(!frontier_128("cache0@128", CacheArm::Cache0).is_zero_removal_alias(zero));
        assert!(!FRONTIER_CONTROL_256.is_zero_removal_alias(zero));

        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            for lane in FRONTIER_FACTORIAL
                .iter()
                .chain(&FRONTIER_EXTENSION)
                .chain(&CACHE_FACTORIAL)
            {
                let counts = plan_arm(&p, lane.arm).unwrap().counts;
                assert!(
                    !lane.is_zero_removal_alias(counts),
                    "{} under {order:?}",
                    lane.label
                );
            }
        }
    }

    /// A census that pushes a lane past the frame fails THAT LANE SET, not a panic and not
    /// a silently truncated plan. The FULL message is asserted: the rejection comes from
    /// `plan_arm`'s always-on validator (which is why `validate_lane_set`'s own frame
    /// branch is belt-and-braces), and only the exact string proves which check fired.
    #[test]
    fn cpu_frontier_lane_set_validator_rejects_over_frame_lanes() {
        let mut p = generate(
            0,
            Census {
                sources: 60,
                ..Census::default()
            },
        )
        .unwrap();
        p.apply_term_order(TermOrder::Locality);
        let direct = plan_arm(&p, CacheArm::All59).unwrap_err();
        assert!(
            direct.ends_with(&format!(
                "exceeds the {UNISKIP_COSET_FRAME_UNITS}-unit frame"
            )),
            "{direct}"
        );
        let over = [frontier_128("all59@128", CacheArm::All59)];
        let err = validate_lane_set(&p, &over).unwrap_err();
        assert_eq!(err, format!("lane all59@128: {direct}"));
    }

    /// The four preregistered facts of each rotation — lane set, flag, log keyword and
    /// round counts — come from ONE value, and the round counts divide their rotations.
    #[test]
    fn cpu_lane_set_selector_is_consistent() {
        assert_eq!(LaneSet::CacheFactorial.lanes().len(), 11);
        assert_eq!(LaneSet::FrontierFactorial.lanes(), &FRONTIER_FACTORIAL);
        assert_eq!(LaneSet::FrontierExtension.lanes(), &FRONTIER_EXTENSION);
        assert_eq!(LaneSet::CacheFactorial.tag(), "CACHE-FACTORIAL");
        assert_eq!(LaneSet::CacheFactorial.rounds_and_warmup(), None);
        assert!(!LaneSet::CacheFactorial.is_frontier());
        for set in [LaneSet::FrontierFactorial, LaneSet::FrontierExtension] {
            assert!(set.is_frontier());
            assert!(set.tag().starts_with("FRONTIER-"));
            let (rounds, warmup) = set.rounds_and_warmup().unwrap();
            let n = set.lanes().len() as u32;
            assert!(rounds.is_multiple_of(n), "{} rounds over {n}", set.flag());
            assert!(warmup.is_multiple_of(n), "{} warmup over {n}", set.flag());
        }
        // The preregistered literals themselves (spec 2.2 / 2.3), not merely their
        // divisibility: the emitter's 90/100 and 94/104 thresholds are keyed to them.
        assert_eq!(
            LaneSet::FrontierFactorial.rounds_and_warmup(),
            Some((100, 10))
        );
        assert_eq!(
            LaneSet::FrontierExtension.rounds_and_warmup(),
            Some((104, 16))
        );
    }

    /// A prefix point no arm names must SAY so. `cache0` is not a neutral placeholder: it
    /// names an empty admitted set, so it would describe a plan admitting seven sources as
    /// admitting none.
    #[test]
    fn cpu_prefix_plan_at_an_unnamed_k_is_not_labelled_cache0() {
        let p = program(TermOrder::Locality);
        let state = plan_prefix(&p, 7).unwrap();
        assert_eq!(state.id, PlanId::Prefix(7));
        assert_eq!(state.id.arm(), None);
        assert_eq!(format!("{}", state.id), "prefix7");
        assert_eq!(state.admitted.len(), 7);
        // The named points still report as themselves, K = 0 included.
        assert_eq!(
            plan_prefix(&p, 0).unwrap().id,
            PlanId::Arm(CacheArm::Cache0)
        );
        assert_eq!(plan_prefix(&p, 48).unwrap().id, PlanId::Arm(CacheArm::K48));
    }

    /// The primary rotation's shape, pinned. A dropped lane or a stray diagnostic arm would
    /// otherwise only show up as a changed round count in a timed log.
    #[test]
    fn cpu_cache_factorial_lane_set() {
        assert_eq!(CACHE_FACTORIAL.len(), 11);
        let labels: Vec<&str> = CACHE_FACTORIAL.iter().map(|l| l.label).collect();
        let mut sorted = labels.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), labels.len(), "lane labels must be unique");
        assert_eq!(
            labels,
            vec![
                "control@256",
                "cache0@256",
                "hot4@256",
                "hot16@256",
                "allrepeat@256",
                "control@128",
                "control_lb@128",
                "cache0@128",
                "hot4@128",
                "hot16@128",
                "allrepeat@128",
            ]
        );
        for lane in CACHE_FACTORIAL {
            assert!(
                !matches!(
                    lane.arm,
                    CacheArm::All59 | CacheArm::E4Rich | CacheArm::E4Top2
                ),
                "{} is a 3B diagnostic and cannot be a primary lane",
                lane.label
            );
        }
    }

    /// The occupancy gate, encoded: every cached lane at 128 must be the BOUNDED body, or
    /// its contrast against the control carries a block-count step.
    #[test]
    fn cpu_cache_factorial_128_cached_lanes_are_bounded() {
        for lane in CACHE_FACTORIAL {
            if lane.block_threads == 128 && lane.arm.uses_cache() {
                assert!(lane.launch_bounds, "{} must be bounded", lane.label);
                assert_eq!(lane.kernel(), LaneKernel::Cached128Lb, "{}", lane.label);
                assert_eq!(lane.blocks_per_sm, 7, "{}", lane.label);
            }
        }
        let kernels: Vec<LaneKernel> = CACHE_FACTORIAL.iter().map(|l| l.kernel()).collect();
        assert!(kernels.contains(&LaneKernel::Pair128));
        assert!(kernels.contains(&LaneKernel::Pair128Lb));
    }

    #[test]
    fn cpu_cache_factorial_kernels_and_tiles() {
        for lane in CACHE_FACTORIAL {
            assert_eq!(
                lane.kernel().is_cached(),
                lane.arm.uses_cache(),
                "{}",
                lane.label
            );
            let expect = if lane.block_threads == 128 { 16 } else { 32 };
            assert_eq!(lane.rows_per_block(), expect, "{}", lane.label);
            assert!(
                lane.kernel().name().starts_with("eval_lsb_pair"),
                "{}",
                lane.label
            );
        }
    }

    /// Admitted sets must be distinct across the lanes of one kernel, or two lanes are the
    /// same experiment under two labels — R3's aliasing failure shape. Checked through the
    /// ONE implementation the runner also calls, so the shipped rotation and the pre-flight
    /// cannot disagree about what counts as an alias.
    #[test]
    fn cpu_cache_factorial_admitted_sets_are_distinct() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            validate_lane_set(&program(order), &CACHE_FACTORIAL).unwrap();
        }
    }
}
