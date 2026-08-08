//! Deterministic synthetic uniskip program with a production-shaped census.
//!
//! Nothing here reads a real GKR layout: the record mix, source count, group
//! shape and coefficient-application count are pinned to the round-0 add/sub
//! layer-0 census, and everything else (operand identities, immediate values,
//! reuse pattern) is generated from `seed`.

use std::fmt;

use crate::abi::*;

/// Census knobs. The defaults are the pinned production-shaped numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Census {
    pub sources: u32,
    pub semantic_terms: u32,
    pub groups: u32,
    pub grouped_atoms: u32,
}

impl Default for Census {
    fn default() -> Self {
        Self {
            sources: 59,
            semantic_terms: 150,
            groups: 25,
            grouped_atoms: 72,
        }
    }
}

/// Coefficient-bank slots the generator keeps live. Cycling all
/// `UNISKIP_COEFF_BANK` slots would change constant-cache behaviour.
pub const SYNTH_LIVE_COEFF_IDS: u32 = 80;
/// Columns of the setup-like window, and the number of terms that read it.
pub const SYNTH_SETUP_COLUMNS: u32 = 4;
pub const SYNTH_SETUP_WINDOW: usize = 4;
pub const SYNTH_E4_WINDOW: usize = 5;
/// Windows 0..4 hold the ordinary BF columns.
pub const SYNTH_ORDINARY_WINDOWS: usize = SYNTH_SETUP_WINDOW;
/// One in `SYNTH_E4_SOURCE_SHARE` non-setup sources is an E4 column (59 -> 11).
const SYNTH_E4_SOURCE_SHARE: u32 = 5;
/// Class split of the ungrouped terms, indexed by term class; scaled by largest
/// remainder when the census is overridden.
const SYNTH_UNGROUPED_WEIGHTS: [u32; 5] = [20, 8, 30, 14, 6];
/// Ungrouped terms emitted between two group headers.
const SYNTH_UNGROUPED_PER_GROUP: usize = 3;
/// Hot slice of each pool, and the reference share it takes.
const SYNTH_HOT_ORDINARY: u16 = 6;
const SYNTH_HOT_E4: u16 = 2;
const SYNTH_HOT_PERIOD: u32 = 5;
const SYNTH_HOT_PER_PERIOD: u32 = 2;
/// Immediate ids a group member can carry: `+1`, `-1`, then the whole table.
const SYNTH_IMMEDIATE_IDS: u32 = UNISKIP_IMMEDIATE_RESERVED as u32 + UNISKIP_MAX_IMMEDIATES as u32;
/// One member in three is a product; the rest are linear.
const SYNTH_MEMBER_PRODUCT_PERIOD: u32 = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WindowKind {
    OrdinaryBf,
    SetupBf,
    E4,
}

impl WindowKind {
    pub fn source_class(self) -> u8 {
        match self {
            WindowKind::OrdinaryBf | WindowKind::SetupBf => UNISKIP_SRC_BF_GLOBAL,
            WindowKind::E4 => UNISKIP_SRC_E4_GLOBAL,
        }
    }
}

/// Per-window allocation spec: `columns` contiguous used columns of one field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WindowSpec {
    pub kind: WindowKind,
    pub columns: u32,
}

/// Measured census of a generated program, printed at startup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusSummary {
    pub records: u32,
    pub semantic_terms: u32,
    pub ungrouped_terms: u32,
    pub groups: u32,
    pub grouped_atoms: u32,
    pub coefficient_applications: u32,
    pub live_coeff_ids: u32,
    pub operand_references: u32,
    pub sources: u32,
    /// Ungrouped term count per term class.
    pub ungrouped_class_counts: [u32; 5],
    /// Group-member count per term class.
    pub member_class_counts: [u32; 5],
    /// Uses of each immediate id (`0` = +1, `1` = -1, `2..` = table).
    pub immediate_id_counts: Vec<u32>,
    /// Operand references naming each source id.
    pub per_source_refs: Vec<u32>,
    /// Sources on the pools' hot slices.
    pub hot_sources: Vec<u16>,
}

impl CensusSummary {
    pub fn hot_references(&self) -> u32 {
        self.hot_sources
            .iter()
            .map(|&s| self.per_source_refs[s as usize])
            .sum()
    }
}

impl fmt::Display for CensusSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hot = self.hot_references();
        let share = 100.0 * f64::from(hot) / f64::from(self.operand_references.max(1));
        let max_refs = self.per_source_refs.iter().copied().max().unwrap_or(0);
        let min_refs = self.per_source_refs.iter().copied().min().unwrap_or(0);
        writeln!(f, "  program records     {}", self.records)?;
        writeln!(f, "  semantic terms      {}", self.semantic_terms)?;
        writeln!(f, "  ungrouped terms     {}", self.ungrouped_terms)?;
        writeln!(f, "  groups              {}", self.groups)?;
        writeln!(f, "  grouped atoms       {}", self.grouped_atoms)?;
        writeln!(f, "  coefficient applic. {}", self.coefficient_applications)?;
        writeln!(f, "  live coeff ids      {}", self.live_coeff_ids)?;
        writeln!(f, "  sources             {}", self.sources)?;
        writeln!(f, "  operand references  {}", self.operand_references)?;
        writeln!(
            f,
            "  ungrouped classes   linear_bf {} linear_e4 {} bf*bf {} bf*e4 {} e4*e4 {}",
            self.ungrouped_class_counts[0],
            self.ungrouped_class_counts[1],
            self.ungrouped_class_counts[2],
            self.ungrouped_class_counts[3],
            self.ungrouped_class_counts[4]
        )?;
        writeln!(
            f,
            "  member classes      linear_bf {} bf*bf {}",
            self.member_class_counts[0], self.member_class_counts[2]
        )?;
        writeln!(f, "  immediate id uses   {:?}", self.immediate_id_counts)?;
        writeln!(f, "  source refs         min {min_refs} max {max_refs}")?;
        write!(
            f,
            "  hot sources         {:?} -> {hot} refs ({share:.1}%)",
            self.hot_sources
        )
    }
}

/// A generated program: the exact wire arrays plus the allocation spec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynthProgram {
    pub program: Vec<UniskipTerm>,
    pub sources: Vec<UniskipSourceRecord>,
    /// CANONICAL BabyBear values; the desc upload converts to the device repr.
    pub immediates_canonical: [u32; UNISKIP_MAX_IMMEDIATES],
    pub windows: [WindowSpec; UNISKIP_WINDOWS],
    pub census: CensusSummary,
}

/// Order of the lowered record stream. `Census` is emission order — the class
/// interleave the generator produces. `Locality` is a permutation of it that clusters
/// records reading the same sources, which changes L1/L2 behaviour for the sources the
/// shared-memory cache does NOT hold. Both are the same records with the same
/// coefficients, so every census quantity and `q` itself are unchanged.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum TermOrder {
    #[default]
    Census,
    Locality,
}

impl TermOrder {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Census => "census",
            Self::Locality => "locality",
        }
    }
}

impl SynthProgram {
    /// Reorder the record stream in place. The unit of movement is a TOP-LEVEL record
    /// — an ungrouped term, or a group header with its members — because a member's
    /// coefficient is the group's immediate and moving it out would change the value.
    /// Members inside a group are clustered too; their sum is over the same field, so
    /// order is irrelevant to it.
    ///
    /// Sound because `q` is a sum of per-term contributions in `bf`/`e4`, where
    /// addition is exactly associative and commutative — `cpu_synth_term_order_keeps_q`
    /// checks that against the full oracle rather than assuming it.
    pub fn apply_term_order(&mut self, order: TermOrder) {
        if order == TermOrder::Census {
            return;
        }
        let mut units: Vec<(Vec<u16>, usize, Vec<UniskipTerm>)> = Vec::new();
        let mut pc = 0usize;
        while pc < self.program.len() {
            let record = self.program[pc];
            let mut unit = vec![record];
            if record.term_class == UNISKIP_CLASS_GROUP_BF {
                let arity = record.source_a as usize;
                let mut members = self.program[pc + 1..pc + 1 + arity].to_vec();
                members.sort_by_key(|m| (m.source_a, m.source_b));
                unit.extend(members);
                pc += arity + 1;
            } else {
                pc += 1;
            }
            let mut key: Vec<u16> = unit
                .iter()
                .skip(usize::from(record.term_class == UNISKIP_CLASS_GROUP_BF))
                .flat_map(|t| [t.source_a, t.source_b])
                .filter(|&s| s != UNISKIP_SOURCE_UNUSED)
                .collect();
            key.sort_unstable();
            key.dedup();
            units.push((key, units.len(), unit));
        }
        units.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
        self.program = units.into_iter().flat_map(|(_, _, unit)| unit).collect();
    }

    /// Binary-product records whose two operands are the SAME source. The generator
    /// emits none, which is why the W = 0 duplicate rule needs
    /// [`Self::force_self_products`] to be exercised at all.
    pub fn self_products(&self) -> u32 {
        self.program
            .iter()
            .filter(|t| Self::is_binary_product(t.term_class) && t.source_a == t.source_b)
            .count() as u32
    }

    fn is_binary_product(term_class: u16) -> bool {
        // BF x E4 cannot self-alias: the operands are drawn from different classes.
        matches!(
            term_class,
            UNISKIP_CLASS_PRODUCT_BF_BF | UNISKIP_CLASS_PRODUCT_E4_E4
        )
    }

    /// Rewrite the first `count` same-class binary products into SELF-products
    /// (`x * x`), touching `source_b` and nothing else. Returns how many it actually
    /// rewrote, which is `count` unless the program holds fewer such records.
    ///
    /// VALIDATION KNOB, not a census knob. The default census has no self-product, so
    /// the LSB mode's W = 0 duplicate rule — a repeated operand inside one term is
    /// produced once, spec 2.5 — is otherwise unreachable on the device. It does move
    /// per-source reference counts (one reference migrates from `source_b` to
    /// `source_a`), so the printed cache plan changes with it and a timing taken under
    /// it is not comparable with the recorded arms.
    pub fn force_self_products(&mut self, count: u32) -> u32 {
        let mut done = 0;
        for term in self.program.iter_mut() {
            if done == count {
                break;
            }
            if Self::is_binary_product(term.term_class) && term.source_a != term.source_b {
                term.source_b = term.source_a;
                done += 1;
            }
        }
        done
    }

    /// Little-endian image of everything that reaches the device wire.
    pub fn wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            self.program.len() * 8 + self.sources.len() * 4 + UNISKIP_MAX_IMMEDIATES * 4,
        );
        for t in &self.program {
            for field in [t.term_class, t.coeff, t.source_a, t.source_b] {
                out.extend_from_slice(&field.to_le_bytes());
            }
        }
        for s in &self.sources {
            out.extend_from_slice(&s.addr.to_le_bytes());
            out.push(s.source_class);
            out.push(s.cache_slot);
        }
        for imm in self.immediates_canonical {
            out.extend_from_slice(&imm.to_le_bytes());
        }
        out
    }
}

/// Round-robin source picker with a fixed hot slice.
struct Pool {
    start: u16,
    len: u16,
    hot: u16,
    picks: u32,
    seed: u32,
}

impl Pool {
    fn new(start: u16, len: u16, hot: u16, seed: u32) -> Self {
        Self {
            start,
            len,
            hot: hot.min(len / 2),
            picks: 0,
            seed,
        }
    }

    /// `SYNTH_HOT_PER_PERIOD` of every `SYNTH_HOT_PERIOD` references land on the
    /// pool's leading hot slice; the rest round-robin the cold remainder, so
    /// every source is used and the hot share stays exactly the intended one.
    fn pick(&mut self) -> u16 {
        let n = self.picks;
        self.picks += 1;
        let hot = u32::from(self.hot);
        if hot == 0 {
            let len = u32::from(self.len);
            return self.start + (n.wrapping_add(self.seed % len) % len) as u16;
        }
        let hot_before = (n / SYNTH_HOT_PERIOD) * SYNTH_HOT_PER_PERIOD
            + (n % SYNTH_HOT_PERIOD).min(SYNTH_HOT_PER_PERIOD);
        let index = if n % SYNTH_HOT_PERIOD < SYNTH_HOT_PER_PERIOD {
            hot_before % hot
        } else {
            let cold = u32::from(self.len) - hot;
            hot + (n - hot_before).wrapping_add(self.seed % cold) % cold
        };
        self.start + index as u16
    }
}

struct Emitter {
    seed: u32,
    ordinary: Pool,
    setup: Pool,
    e4: Pool,
    refs: Vec<u32>,
    coeff_cursor: u32,
    live_coeffs: Vec<bool>,
    members: u32,
    immediate_id_counts: Vec<u32>,
    class_seen: [u32; 5],
    ungrouped_class_counts: [u32; 5],
    member_class_counts: [u32; 5],
}

impl Emitter {
    fn take(&mut self, pool: PoolId) -> u16 {
        let id = match pool {
            PoolId::Ordinary => self.ordinary.pick(),
            PoolId::Setup => self.setup.pick(),
            PoolId::E4 => self.e4.pick(),
        };
        self.refs[id as usize] += 1;
        id
    }

    fn next_coeff(&mut self) -> u16 {
        let id = self.coeff_cursor % SYNTH_LIVE_COEFF_IDS;
        self.coeff_cursor += 1;
        self.live_coeffs[id as usize] = true;
        id as u16
    }

    fn next_immediate(&mut self) -> u16 {
        let id = self.members.wrapping_add(self.seed % SYNTH_IMMEDIATE_IDS) % SYNTH_IMMEDIATE_IDS;
        self.immediate_id_counts[id as usize] += 1;
        id as u16
    }
}

#[derive(Clone, Copy)]
enum PoolId {
    Ordinary,
    Setup,
    E4,
}

pub fn generate(seed: u32, cfg: Census) -> Result<SynthProgram, String> {
    let ungrouped = cfg
        .semantic_terms
        .checked_sub(cfg.grouped_atoms)
        .ok_or_else(|| {
            format!(
                "grouped atoms {} exceed semantic terms {}",
                cfg.grouped_atoms, cfg.semantic_terms
            )
        })?;
    if cfg.groups == 0 && cfg.grouped_atoms > 0 {
        return Err(format!(
            "{} grouped atoms need at least one group",
            cfg.grouped_atoms
        ));
    }
    let (min_arity, extra_arity) = match cfg.grouped_atoms.checked_div(cfg.groups) {
        Some(min_arity) => (min_arity, cfg.grouped_atoms % cfg.groups),
        None => (0, 0),
    };
    if cfg.groups > 0 && min_arity < 2 {
        return Err(format!(
            "{} grouped atoms over {} groups gives arity {min_arity}; a group needs at least 2 members",
            cfg.grouped_atoms, cfg.groups
        ));
    }
    let records = ungrouped
        .checked_add(cfg.groups)
        .and_then(|r| r.checked_add(cfg.grouped_atoms))
        .ok_or_else(|| {
            format!(
                "{ungrouped} ungrouped terms + {} group headers + {} grouped atoms overflow the u32 record count",
                cfg.groups, cfg.grouped_atoms
            )
        })?;
    if records as usize > UNISKIP_PROGRAM_CAPACITY {
        return Err(format!(
            "{records} program records exceed UNISKIP_PROGRAM_CAPACITY {UNISKIP_PROGRAM_CAPACITY}"
        ));
    }
    if cfg.sources as usize > UNISKIP_SOURCE_CAPACITY {
        return Err(format!(
            "{} sources exceed UNISKIP_SOURCE_CAPACITY {UNISKIP_SOURCE_CAPACITY}",
            cfg.sources
        ));
    }
    let non_setup = cfg
        .sources
        .checked_sub(SYNTH_SETUP_COLUMNS)
        .filter(|rest| *rest >= SYNTH_E4_SOURCE_SHARE)
        .ok_or_else(|| {
            format!(
                "{} sources cannot cover {SYNTH_SETUP_COLUMNS} setup columns plus at least {SYNTH_E4_SOURCE_SHARE} more",
                cfg.sources
            )
        })?;
    let e4_columns = non_setup / SYNTH_E4_SOURCE_SHARE;
    let ordinary_columns = non_setup - e4_columns;
    if (ordinary_columns as usize) < SYNTH_ORDINARY_WINDOWS {
        return Err(format!(
            "{ordinary_columns} ordinary columns cannot fill {SYNTH_ORDINARY_WINDOWS} windows"
        ));
    }

    let mut windows = [WindowSpec {
        kind: WindowKind::OrdinaryBf,
        columns: 0,
    }; UNISKIP_WINDOWS];
    for (w, spec) in windows.iter_mut().enumerate().take(SYNTH_ORDINARY_WINDOWS) {
        let share = ordinary_columns / SYNTH_ORDINARY_WINDOWS as u32;
        let extra = u32::from((w as u32) < ordinary_columns % SYNTH_ORDINARY_WINDOWS as u32);
        spec.columns = share + extra;
    }
    windows[SYNTH_SETUP_WINDOW] = WindowSpec {
        kind: WindowKind::SetupBf,
        columns: SYNTH_SETUP_COLUMNS,
    };
    windows[SYNTH_E4_WINDOW] = WindowSpec {
        kind: WindowKind::E4,
        columns: e4_columns,
    };
    for (w, spec) in windows.iter().enumerate() {
        if spec.columns as usize > UNISKIP_MAX_WINDOW_COLUMNS {
            return Err(format!("window {w} needs {} columns, over the {UNISKIP_MAX_WINDOW_COLUMNS}-column addr field", spec.columns));
        }
    }

    let mut sources = Vec::with_capacity(cfg.sources as usize);
    for (w, spec) in windows.iter().enumerate() {
        for column in 0..spec.columns as usize {
            sources.push(UniskipSourceRecord {
                addr: source_addr(w, column),
                source_class: spec.kind.source_class(),
                cache_slot: UNISKIP_CACHE_SLOT_NONE,
            });
        }
    }
    debug_assert_eq!(sources.len(), cfg.sources as usize);

    let class_counts = scale_counts(ungrouped, SYNTH_UNGROUPED_WEIGHTS);
    if class_counts[UNISKIP_CLASS_LINEAR_BF as usize] < 2
        || class_counts[UNISKIP_CLASS_PRODUCT_BF_BF as usize] < 2
    {
        return Err(format!(
            "{ungrouped} ungrouped terms give too few BF terms to place the {SYNTH_SETUP_COLUMNS} setup-window references"
        ));
    }

    let mut emitter = Emitter {
        seed,
        ordinary: Pool::new(0, ordinary_columns as u16, SYNTH_HOT_ORDINARY, seed),
        setup: Pool::new(ordinary_columns as u16, SYNTH_SETUP_COLUMNS as u16, 0, seed),
        e4: Pool::new(
            (ordinary_columns + SYNTH_SETUP_COLUMNS) as u16,
            e4_columns as u16,
            SYNTH_HOT_E4,
            seed,
        ),
        refs: vec![0; cfg.sources as usize],
        coeff_cursor: seed % SYNTH_LIVE_COEFF_IDS,
        live_coeffs: vec![false; UNISKIP_COEFF_BANK],
        members: 0,
        immediate_id_counts: vec![0; SYNTH_IMMEDIATE_IDS as usize],
        class_seen: [0; 5],
        ungrouped_class_counts: class_counts,
        member_class_counts: [0; 5],
    };

    let order = class_order(class_counts);
    let mut program = Vec::with_capacity(records as usize);
    let mut next_term = 0usize;
    let mut next_group = 0u32;
    while next_term < order.len() || next_group < cfg.groups {
        for _ in 0..SYNTH_UNGROUPED_PER_GROUP {
            if next_term == order.len() {
                break;
            }
            program.push(ungrouped_term(&mut emitter, order[next_term], class_counts));
            next_term += 1;
        }
        if next_group < cfg.groups {
            let arity = min_arity + u32::from(bresenham_step(next_group, extra_arity, cfg.groups));
            program.push(UniskipTerm {
                term_class: UNISKIP_CLASS_GROUP_BF,
                coeff: emitter.next_coeff(),
                source_a: arity as u16,
                source_b: UNISKIP_SOURCE_UNUSED,
            });
            for _ in 0..arity {
                program.push(group_member(&mut emitter));
            }
            next_group += 1;
        }
    }
    debug_assert_eq!(program.len(), records as usize);

    if let Some(id) = emitter.refs.iter().position(|&r| r == 0) {
        let rec = sources[id];
        return Err(format!(
            "source {id} (window {}, column {}) is never referenced — the census is too small for {} sources",
            addr_window(rec.addr),
            addr_column(rec.addr),
            cfg.sources
        ));
    }

    let immediates_canonical = core::array::from_fn(|i| immediate_value(seed, i));
    let hot_sources = (0..emitter.ordinary.hot)
        .map(|i| emitter.ordinary.start + i)
        .chain((0..emitter.e4.hot).map(|i| emitter.e4.start + i))
        .collect();
    let census = CensusSummary {
        records,
        semantic_terms: cfg.semantic_terms,
        ungrouped_terms: ungrouped,
        groups: cfg.groups,
        grouped_atoms: cfg.grouped_atoms,
        coefficient_applications: ungrouped + cfg.groups,
        live_coeff_ids: emitter.live_coeffs.iter().filter(|&&l| l).count() as u32,
        operand_references: emitter.refs.iter().sum(),
        sources: cfg.sources,
        ungrouped_class_counts: emitter.ungrouped_class_counts,
        member_class_counts: emitter.member_class_counts,
        immediate_id_counts: emitter.immediate_id_counts,
        per_source_refs: emitter.refs,
        hot_sources,
    };

    Ok(SynthProgram {
        program,
        sources,
        immediates_canonical,
        windows,
        census,
    })
}

fn ungrouped_term(emitter: &mut Emitter, term_class: u16, class_counts: [u32; 5]) -> UniskipTerm {
    let seen = emitter.class_seen[term_class as usize];
    emitter.class_seen[term_class as usize] += 1;
    // Two terms per BF class read the setup-like window: the first, and the one
    // halfway through the class.
    let setup = seen == 0 || seen == class_counts[term_class as usize] / 2;
    let coeff = emitter.next_coeff();
    let (source_a, source_b) = match term_class {
        UNISKIP_CLASS_LINEAR_BF => {
            let a = emitter.take(if setup {
                PoolId::Setup
            } else {
                PoolId::Ordinary
            });
            (a, UNISKIP_SOURCE_UNUSED)
        }
        UNISKIP_CLASS_LINEAR_E4 => (emitter.take(PoolId::E4), UNISKIP_SOURCE_UNUSED),
        UNISKIP_CLASS_PRODUCT_BF_BF => {
            let a = emitter.take(PoolId::Ordinary);
            let b = emitter.take(if setup {
                PoolId::Setup
            } else {
                PoolId::Ordinary
            });
            (a, b)
        }
        UNISKIP_CLASS_PRODUCT_BF_E4 => {
            let a = emitter.take(PoolId::Ordinary);
            (a, emitter.take(PoolId::E4))
        }
        UNISKIP_CLASS_PRODUCT_E4_E4 => {
            let a = emitter.take(PoolId::E4);
            (a, emitter.take(PoolId::E4))
        }
        other => unreachable!("class {other} is not an ungrouped term class"),
    };
    UniskipTerm {
        term_class,
        coeff,
        source_a,
        source_b,
    }
}

fn group_member(emitter: &mut Emitter) -> UniskipTerm {
    let product = emitter
        .members
        .wrapping_add(emitter.seed % SYNTH_MEMBER_PRODUCT_PERIOD)
        % SYNTH_MEMBER_PRODUCT_PERIOD
        == SYNTH_MEMBER_PRODUCT_PERIOD - 1;
    let coeff = emitter.next_immediate();
    emitter.members += 1;
    let term_class = if product {
        UNISKIP_CLASS_PRODUCT_BF_BF
    } else {
        UNISKIP_CLASS_LINEAR_BF
    };
    emitter.member_class_counts[term_class as usize] += 1;
    let source_a = emitter.take(PoolId::Ordinary);
    let source_b = if product {
        emitter.take(PoolId::Ordinary)
    } else {
        UNISKIP_SOURCE_UNUSED
    };
    UniskipTerm {
        term_class,
        coeff,
        source_a,
        source_b,
    }
}

/// Canonical BabyBear value of immediate slot `i`, in the shape of the device
/// init generator (nonzero, seed-dependent).
fn immediate_value(seed: u32, index: usize) -> u32 {
    const ORDER: u64 = 0x7800_0001;
    ((u64::from(seed) + index as u64 * 17 + 0x101) % (ORDER - 1) + 1) as u32
}

/// Largest-remainder scaling of `weights` to `total`.
fn scale_counts(total: u32, weights: [u32; 5]) -> [u32; 5] {
    let sum: u32 = weights.iter().sum();
    let mut counts = [0u32; 5];
    let mut remainders = [(0u32, 0usize); 5];
    for (i, &w) in weights.iter().enumerate() {
        let exact = u64::from(total) * u64::from(w);
        counts[i] = (exact / u64::from(sum)) as u32;
        remainders[i] = ((exact % u64::from(sum)) as u32, i);
    }
    let mut left = total - counts.iter().sum::<u32>();
    remainders.sort_by_key(|&(rem, i)| (std::cmp::Reverse(rem), i));
    for &(_, i) in remainders.iter() {
        if left == 0 {
            break;
        }
        counts[i] += 1;
        left -= 1;
    }
    counts
}

/// Interleaves the classes by always emitting the one with the most left.
fn class_order(counts: [u32; 5]) -> Vec<u16> {
    let mut left = counts;
    let total: u32 = counts.iter().sum();
    let mut out = Vec::with_capacity(total as usize);
    for _ in 0..total {
        let class = (0..5)
            .max_by_key(|&i| (left[i], std::cmp::Reverse(i)))
            .unwrap();
        left[class] -= 1;
        out.push(class as u16);
    }
    out
}

/// True for exactly `extra` of the `total` indices, spread evenly.
fn bresenham_step(index: u32, extra: u32, total: u32) -> bool {
    (index + 1) * extra / total > index * extra / total
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    fn required_class(term_class: u16) -> (u8, Option<u8>) {
        match term_class {
            UNISKIP_CLASS_LINEAR_BF => (UNISKIP_SRC_BF_GLOBAL, None),
            UNISKIP_CLASS_LINEAR_E4 => (UNISKIP_SRC_E4_GLOBAL, None),
            UNISKIP_CLASS_PRODUCT_BF_BF => (UNISKIP_SRC_BF_GLOBAL, Some(UNISKIP_SRC_BF_GLOBAL)),
            UNISKIP_CLASS_PRODUCT_BF_E4 => (UNISKIP_SRC_BF_GLOBAL, Some(UNISKIP_SRC_E4_GLOBAL)),
            UNISKIP_CLASS_PRODUCT_E4_E4 => (UNISKIP_SRC_E4_GLOBAL, Some(UNISKIP_SRC_E4_GLOBAL)),
            other => panic!("class {other} has no operands"),
        }
    }

    #[derive(Default)]
    struct Walk {
        semantic_terms: u32,
        ungrouped: u32,
        groups: u32,
        members: u32,
        coefficient_applications: u32,
        operand_references: u32,
        used: Vec<bool>,
    }

    /// Walks the record grammar: a group header carries an arity in `source_a`
    /// (never a source id) and is followed by exactly that many BF member
    /// records; members never nest; the walk ends on `record_count`.
    fn walk(p: &SynthProgram) -> Walk {
        let mut w = Walk {
            used: vec![false; p.sources.len()],
            ..Default::default()
        };
        let check_operands = |w: &mut Walk, term: &UniskipTerm| {
            let (class_a, class_b) = required_class(term.term_class);
            for (source, want) in [(term.source_a, Some(class_a)), (term.source_b, class_b)] {
                match want {
                    Some(want) => {
                        let id = source as usize;
                        assert!(
                            id < p.sources.len(),
                            "operand {source} is not a live source"
                        );
                        assert_eq!(
                            p.sources[id].source_class, want,
                            "operand {source} has the wrong field"
                        );
                        w.used[id] = true;
                        w.operand_references += 1;
                    }
                    None => assert_eq!(
                        source, UNISKIP_SOURCE_UNUSED,
                        "unused operand slot must be the sentinel"
                    ),
                }
            }
        };

        let mut pc = 0usize;
        while pc < p.program.len() {
            let record = p.program[pc];
            if record.term_class == UNISKIP_CLASS_GROUP_BF {
                let arity = record.source_a as usize;
                assert!(arity >= 2, "group at {pc} has arity {arity}");
                assert!((record.coeff as usize) < UNISKIP_COEFF_BANK);
                assert_eq!(record.source_b, UNISKIP_SOURCE_UNUSED);
                assert!(
                    pc + arity < p.program.len(),
                    "group at {pc} runs past the program"
                );
                for j in 1..=arity {
                    let member = p.program[pc + j];
                    assert!(
                        member.term_class == UNISKIP_CLASS_LINEAR_BF
                            || member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF,
                        "group member {j} has class {}",
                        member.term_class
                    );
                    assert!(
                        (member.coeff as u32) < SYNTH_IMMEDIATE_IDS,
                        "member immediate id {} is out of range",
                        member.coeff
                    );
                    check_operands(&mut w, &member);
                    w.members += 1;
                }
                w.groups += 1;
                w.coefficient_applications += 1;
                w.semantic_terms += arity as u32;
                pc += arity + 1;
            } else {
                assert!(record.term_class <= UNISKIP_CLASS_PRODUCT_E4_E4);
                assert!((record.coeff as usize) < UNISKIP_COEFF_BANK);
                check_operands(&mut w, &record);
                w.ungrouped += 1;
                w.coefficient_applications += 1;
                w.semantic_terms += 1;
                pc += 1;
            }
        }
        assert_eq!(
            pc,
            p.program.len(),
            "the walk must land exactly on record_count"
        );
        w
    }

    #[test]
    fn cpu_synth_deterministic() {
        let a = generate(11, Census::default()).unwrap();
        let b = generate(11, Census::default()).unwrap();
        assert_eq!(a.wire_bytes(), b.wire_bytes());
        assert_eq!(a, b);
        let c = generate(12, Census::default()).unwrap();
        assert_ne!(a.wire_bytes(), c.wire_bytes());
        assert_eq!(a.census.records, c.census.records);
    }

    /// The seed offsets every cursor; the extremes must not overflow, and the
    /// census must not drift with them (the seed is reduced by each cursor's
    /// modulus, so no phase hiccups at the wrap point). Runs with overflow checks
    /// on under the dev profile.
    #[test]
    fn cpu_synth_seed_extremes() {
        for seed in [u32::MAX, u32::MAX - 1, 0x8000_0000, u32::MAX / 2] {
            let p = generate(seed, Census::default()).unwrap();
            assert_eq!(p.census.records, 175);
            assert_eq!(p.census.live_coeff_ids, 80);
            assert_eq!(p.census.operand_references, 224);
            assert_eq!(p.census.member_class_counts[0], 48);
            assert_eq!(p.census.member_class_counts[2], 24);
            assert_eq!(p.census.immediate_id_counts, vec![4; 18]);
            assert!(p.census.per_source_refs.iter().all(|&r| r > 0));
            walk(&p);
            assert_eq!(
                generate(seed, Census::default()).unwrap().wire_bytes(),
                p.wire_bytes()
            );
        }
    }

    #[test]
    fn cpu_synth_census() {
        for seed in [0u32, 1, 7, 4242] {
            let p = generate(seed, Census::default()).unwrap();
            let c = &p.census;
            assert_eq!(c.records, 175);
            assert_eq!(p.program.len(), 175);
            assert_eq!(c.semantic_terms, 150);
            assert_eq!(c.ungrouped_terms, 78);
            assert_eq!(c.groups, 25);
            assert_eq!(c.grouped_atoms, 72);
            assert_eq!(c.coefficient_applications, 103);
            assert_eq!(c.live_coeff_ids, 80);
            assert_eq!(c.sources, 59);
            assert_eq!(p.sources.len(), 59);
            assert_eq!(c.ungrouped_class_counts, [20, 8, 30, 14, 6]);
            assert_eq!(c.member_class_counts[0] + c.member_class_counts[2], 72);
            assert!(
                c.immediate_id_counts.iter().all(|&n| n > 0),
                "every immediate id must be exercised"
            );

            // Window kinds and spans: 4 ordinary BF, 1 setup BF, 1 E4.
            let columns: Vec<u32> = p.windows.iter().map(|w| w.columns).collect();
            assert_eq!(columns, vec![11, 11, 11, 11, 4, 11]);
            assert_eq!(p.windows[SYNTH_SETUP_WINDOW].kind, WindowKind::SetupBf);
            assert_eq!(p.windows[SYNTH_E4_WINDOW].kind, WindowKind::E4);
            let bf_sources = p
                .sources
                .iter()
                .filter(|s| s.source_class == UNISKIP_SRC_BF_GLOBAL)
                .count();
            assert_eq!(bf_sources, 48);
            assert_eq!(p.sources.len() - bf_sources, 11);

            // addr bijection + per-window field homogeneity.
            let mut seen = std::collections::HashSet::new();
            let mut per_window_class = [None; UNISKIP_WINDOWS];
            for (id, rec) in p.sources.iter().enumerate() {
                let window = addr_window(rec.addr);
                let column = addr_column(rec.addr);
                assert!(
                    column < p.windows[window].columns as usize,
                    "source {id} column {column} outside its span"
                );
                assert_eq!(rec.addr, source_addr(window, column));
                assert_eq!(rec.cache_slot, UNISKIP_CACHE_SLOT_NONE);
                assert!(
                    seen.insert((window, column)),
                    "duplicate source at ({window}, {column})"
                );
                let want = per_window_class[window].get_or_insert(rec.source_class);
                assert_eq!(
                    *want, rec.source_class,
                    "window {window} mixes field classes"
                );
                assert_eq!(rec.source_class, p.windows[window].kind.source_class());
            }
            assert_eq!(seen.len(), 59);

            let w = walk(&p);
            assert_eq!(w.groups, 25);
            assert_eq!(w.members, 72);
            assert_eq!(w.ungrouped, 78);
            assert_eq!(w.semantic_terms, 150);
            assert_eq!(w.coefficient_applications, 103);
            assert_eq!(w.operand_references, c.operand_references);
            assert_eq!(w.operand_references, 224);
            assert!(w.used.iter().all(|&u| u), "every source must be referenced");
            assert_eq!(c.per_source_refs.iter().sum::<u32>(), 224);
            assert!(c.per_source_refs.iter().all(|&r| r > 0));

            // Exactly 4 BF terms read the setup window: 2 linear, 2 product-B.
            let setup_ids: Vec<u16> = p
                .sources
                .iter()
                .enumerate()
                .filter(|(_, r)| addr_window(r.addr) == SYNTH_SETUP_WINDOW)
                .map(|(id, _)| id as u16)
                .collect();
            assert_eq!(setup_ids.len(), 4);
            let linear = p
                .program
                .iter()
                .filter(|t| {
                    t.term_class == UNISKIP_CLASS_LINEAR_BF && setup_ids.contains(&t.source_a)
                })
                .count();
            let product_b = p
                .program
                .iter()
                .filter(|t| {
                    t.term_class == UNISKIP_CLASS_PRODUCT_BF_BF && setup_ids.contains(&t.source_b)
                })
                .count();
            let product_a = p
                .program
                .iter()
                .filter(|t| {
                    t.term_class == UNISKIP_CLASS_PRODUCT_BF_BF && setup_ids.contains(&t.source_a)
                })
                .count();
            assert_eq!((linear, product_b, product_a), (2, 2, 0));
            for id in setup_ids {
                assert_eq!(
                    c.per_source_refs[id as usize], 1,
                    "setup column {id} is read once"
                );
            }

            // Skewed reuse: the 8 hot sources take ~40% of the references.
            assert_eq!(c.hot_sources.len(), 8);
            let share = f64::from(c.hot_references()) / f64::from(c.operand_references);
            assert!((0.35..0.45).contains(&share), "hot share {share}");
        }
    }

    #[test]
    fn cpu_synth_capacity_errors() {
        let over_program = Census {
            semantic_terms: 240,
            grouped_atoms: 120,
            groups: 40,
            ..Census::default()
        };
        assert!(generate(0, over_program)
            .unwrap_err()
            .contains("UNISKIP_PROGRAM_CAPACITY"));
        let over_sources = Census {
            sources: 65,
            ..Census::default()
        };
        assert!(generate(0, over_sources)
            .unwrap_err()
            .contains("UNISKIP_SOURCE_CAPACITY"));
        let bad_groups = Census {
            groups: 40,
            grouped_atoms: 72,
            ..Census::default()
        };
        assert!(generate(0, bad_groups)
            .unwrap_err()
            .contains("at least 2 members"));
        let too_many_atoms = Census {
            semantic_terms: 50,
            grouped_atoms: 72,
            ..Census::default()
        };
        assert!(generate(0, too_many_atoms)
            .unwrap_err()
            .contains("exceed semantic terms"));
        let thin_sources = Census {
            sources: 8,
            ..Census::default()
        };
        assert!(generate(0, thin_sources).is_err());
        assert!(generate(0, OVERFLOWING_RECORDS)
            .unwrap_err()
            .contains("overflow the u32 record count"));
    }

    /// The record count is `semantic_terms + groups`; every field is a CLI-controlled
    /// `u32`, so a valid `semantic_terms - grouped_atoms` can still be followed by an
    /// addition that leaves `u32`. Dev used to panic here and release used to wrap into
    /// a small `records` that slipped past the capacity check.
    const OVERFLOWING_RECORDS: Census = Census {
        sources: 59,
        semantic_terms: 4294967295,
        groups: 102,
        grouped_atoms: 4294967195,
    };

    #[test]
    fn cpu_synth_record_count_overflow_is_rejected() {
        // Everything before the addition must succeed, or the case would not reach it.
        assert_eq!(
            OVERFLOWING_RECORDS.semantic_terms - OVERFLOWING_RECORDS.grouped_atoms,
            100
        );
        assert!(OVERFLOWING_RECORDS.grouped_atoms / OVERFLOWING_RECORDS.groups >= 2);
        let err = generate(0, OVERFLOWING_RECORDS).unwrap_err();
        assert!(err.contains("overflow the u32 record count"), "{err}");
        // Release must not wrap into a small record count that passes the capacity gate.
        assert!(!err.contains("UNISKIP_PROGRAM_CAPACITY"), "{err}");
    }

    /// `locality` must be a PERMUTATION of the census stream at the record level and
    /// leave every census invariant standing — the whole point is that it changes only
    /// the order operands are touched in.
    #[test]
    fn cpu_synth_term_order_is_a_permutation() {
        for seed in [0u32, 7, 4242] {
            let census = generate(seed, Census::default()).unwrap();
            let mut local = census.clone();
            local.apply_term_order(TermOrder::Locality);

            assert_ne!(local.program, census.program, "locality changed nothing");
            assert_eq!(local.sources, census.sources);
            assert_eq!(local.census, census.census);
            assert_eq!(local.program.len(), census.program.len());

            let sorted = |p: &SynthProgram| {
                let mut records: Vec<(u16, u16, u16, u16)> = p
                    .program
                    .iter()
                    .map(|t| (t.term_class, t.coeff, t.source_a, t.source_b))
                    .collect();
                records.sort_unstable();
                records
            };
            assert_eq!(sorted(&local), sorted(&census));

            // The grammar still walks, and every derived census quantity re-derives to
            // the same numbers off the reordered stream.
            let w = walk(&local);
            assert_eq!(w.groups, census.census.groups);
            assert_eq!(w.members, census.census.grouped_atoms);
            assert_eq!(w.ungrouped, census.census.ungrouped_terms);
            assert_eq!(w.semantic_terms, census.census.semantic_terms);
            assert_eq!(
                w.coefficient_applications,
                census.census.coefficient_applications
            );
            assert_eq!(w.operand_references, census.census.operand_references);
            assert!(w.used.iter().all(|&u| u));

            // Deterministic, and idempotent — sorting an already-sorted stream is a
            // no-op, so a re-applied order cannot drift.
            let mut again = census.clone();
            again.apply_term_order(TermOrder::Locality);
            assert_eq!(again.program, local.program);
            again.apply_term_order(TermOrder::Locality);
            assert_eq!(again.program, local.program);

            // It really does cluster: the number of times the leading source id changes
            // between consecutive top-level records drops.
            let leads = |p: &SynthProgram| {
                let mut out = Vec::new();
                let mut pc = 0usize;
                while pc < p.program.len() {
                    let record = p.program[pc];
                    let arity = if record.term_class == UNISKIP_CLASS_GROUP_BF {
                        record.source_a as usize
                    } else {
                        0
                    };
                    let first = if arity > 0 {
                        p.program[pc + 1..pc + 1 + arity]
                            .iter()
                            .map(|m| m.source_a)
                            .min()
                            .unwrap()
                    } else {
                        record.source_a
                    };
                    out.push(first);
                    pc += arity + 1;
                }
                out.windows(2).filter(|w| w[0] != w[1]).count()
            };
            assert!(
                leads(&local) < leads(&census),
                "locality did not reduce source switches"
            );
        }
    }

    /// The reorder is only legal because `q` is a sum whose terms commute. Check it
    /// against the full oracle at a geometry small enough to run on the CPU, in both
    /// eq modes, rather than asserting the algebra.
    /// The duplicate-rule knob: the default census has no self-product (so the
    /// recorded arms' reference counts are unaffected by the rule existing), the
    /// rewrite touches only `source_b`, and it genuinely changes `q` — so a device run
    /// under it is a real test of the LSB accessor's short-circuit and not a no-op.
    #[test]
    fn cpu_synth_force_self_products() {
        use crate::abi::SourceLayout;
        use crate::geometry::Geometry;
        use crate::reference::eval_q;

        let base = generate(7, Census::default()).unwrap();
        assert_eq!(base.self_products(), 0);

        let mut forced = base.clone();
        assert_eq!(forced.force_self_products(8), 8);
        assert_eq!(forced.self_products(), 8);
        for (a, b) in base.program.iter().zip(&forced.program) {
            assert_eq!(
                (a.term_class, a.coeff, a.source_a),
                (b.term_class, b.coeff, b.source_a)
            );
        }

        let geometry = Geometry::new(10).unwrap();
        for layout in [SourceLayout::PlaneMajor, SourceLayout::LsbGroup] {
            assert_ne!(
                eval_q(&forced, &geometry, 7, false, layout),
                eval_q(&base, &geometry, 7, false, layout),
                "{layout:?}"
            );
        }

        // Saturates at the number of same-class binary products rather than lying.
        let mut all = base.clone();
        let available = all.force_self_products(u32::MAX);
        assert!(available >= 8, "{available}");
        assert_eq!(all.self_products(), available);
        assert_eq!(all.force_self_products(1), 0);
    }

    #[test]
    fn cpu_synth_term_order_keeps_q() {
        use crate::geometry::Geometry;
        use crate::reference::eval_q;

        let geometry = Geometry::new(10).unwrap();
        let census = generate(7, Census::default()).unwrap();
        let mut local = census.clone();
        local.apply_term_order(TermOrder::Locality);
        for source_layout in [SourceLayout::PlaneMajor, SourceLayout::LsbGroup] {
            for flat_eq in [false, true] {
                assert_eq!(
                    eval_q(&local, &geometry, 7, flat_eq, source_layout),
                    eval_q(&census, &geometry, 7, flat_eq, source_layout),
                    "term order changed q ({source_layout:?}, flat_eq {flat_eq})"
                );
            }
        }
    }

    #[test]
    fn cpu_synth_scales_off_default() {
        let cfg = Census {
            sources: 34,
            semantic_terms: 90,
            groups: 12,
            grouped_atoms: 36,
        };
        let p = generate(3, cfg).unwrap();
        assert_eq!(p.census.records, 54 + 12 + 36);
        assert_eq!(p.census.ungrouped_class_counts.iter().sum::<u32>(), 54);
        assert_eq!(p.sources.len(), 34);
        let w = walk(&p);
        assert_eq!(w.semantic_terms, 90);
        assert!(w.used.iter().all(|&u| u));
    }
}
