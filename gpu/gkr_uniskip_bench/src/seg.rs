//! The v3 R7 dealer: the host-side split of one ordered term program into
//! [`UNISKIP_SEG_K`] atom-preserving per-warp lists, plus the coset prologue's owner
//! striping.
//!
//! SEMANTICS. An ATOM is the unit a warp must own whole: a group header with all its
//! members, or any other single record. Splitting one would either lose the group's
//! accumulator or move a member's immediate away from its header, so the dealer's unit of
//! movement is the atom and never the record. The deal is CAPTURE-BLIND — `cache_slot` is
//! ignored and every operand resolution is priced as uncached — because a warp's list is
//! chosen before any arm is known, so one deal serves every cache arm.
//!
//! COST MODEL. Per record: `(width(a) + width(b)) * 7` for the chain, plus the class's
//! multiply, plus the coefficient application. A group HEADER resolves no operand — its
//! `source_a` is the member arity, not a source id — so it carries the apply cost alone.
//!
//! DRIFT KEY. The dealt record stream is fingerprinted with FNV-1a 64 rendered as 16
//! lowercase hex, not sha256: the crate has no hash dependency and the emitter side must
//! recompute the same value from a `struct.pack("<4H", ...)` walk in ten lines.

use crate::abi::*;
use crate::coset_cache::{CacheArmState, PrologueOrder};
use crate::synth::SynthProgram;

pub use crate::abi::UNISKIP_SEG_K;

/// Chain cost of producing one `bf` component's coset pair.
const SEG_CHAIN_COST: u64 = 7;

/// One warp's share of the program: the atom boundaries, the records themselves, and the
/// cost the dealer balanced on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SegPlan {
    /// Record indices into [`Self::program`]; `list_offset[k]..list_offset[k + 1]` is warp `k`.
    pub list_offset: [u16; UNISKIP_SEG_K + 1],
    /// The lists concatenated, atom order preserved inside each.
    pub program: Vec<UniskipTerm>,
    pub predicted_cost: [u64; UNISKIP_SEG_K],
}

/// Split the ORDERED program into [`UNISKIP_SEG_K`] lists, each whole atoms, by greedy
/// least-loaded assignment in program order.
pub fn deal(program: &SynthProgram) -> Result<SegPlan, String> {
    let atoms = atoms(&program.program, &program.sources)?;
    if atoms.len() < UNISKIP_SEG_K {
        return Err(format!(
            "{} atoms cannot fill {UNISKIP_SEG_K} nonempty lists",
            atoms.len()
        ));
    }

    let mut predicted_cost = [0u64; UNISKIP_SEG_K];
    let mut lists: [Vec<Atom>; UNISKIP_SEG_K] = core::array::from_fn(|_| Vec::new());
    for atom in atoms {
        let owner = (0..UNISKIP_SEG_K)
            .min_by_key(|&k| (predicted_cost[k], k))
            .expect("UNISKIP_SEG_K is nonzero");
        predicted_cost[owner] += atom.cost;
        lists[owner].push(atom);
    }

    let mut dealt = Vec::with_capacity(program.program.len());
    let mut list_offset = [0u16; UNISKIP_SEG_K + 1];
    for (k, list) in lists.iter().enumerate() {
        for atom in list {
            dealt.extend_from_slice(&program.program[atom.pc..atom.pc + atom.records]);
        }
        list_offset[k + 1] = u16::try_from(dealt.len())
            .map_err(|_| format!("{} dealt records exceed the u16 offset", dealt.len()))?;
    }
    if dealt.len() > UNISKIP_PROGRAM_CAPACITY {
        return Err(format!(
            "{} dealt records exceed UNISKIP_PROGRAM_CAPACITY {UNISKIP_PROGRAM_CAPACITY}",
            dealt.len()
        ));
    }

    Ok(SegPlan {
        list_offset,
        program: dealt,
        predicted_cost,
    })
}

/// Assign every prologue row an owner warp, least-loaded by component width, in production
/// walk order. Consumers match the pairs onto rows by source id, never by position.
pub fn stripe_prologue(state: &CacheArmState) -> Vec<(u16, u8)> {
    let mut load = [0u32; UNISKIP_SEG_K];
    let mut out = Vec::new();
    for row in state.prologue_in(PrologueOrder::E4First) {
        let owner = (0..UNISKIP_SEG_K)
            .min_by_key(|&k| (load[k], k))
            .expect("UNISKIP_SEG_K is nonzero");
        load[owner] += component_width(state.sources[row.source as usize].source_class);
        out.push((row.source, owner as u8));
    }
    out
}

/// Per-warp component and store-instruction sums of an owner striping: an `e4` row is 4
/// components and 2 `STL.128`, a `bf` row 1 component and 1 `STL.64`.
pub fn owner_sums(
    owners: &[(u16, u8)],
    state: &CacheArmState,
) -> Result<([u32; UNISKIP_SEG_K], [u32; UNISKIP_SEG_K]), String> {
    let mut components = [0u32; UNISKIP_SEG_K];
    let mut stores = [0u32; UNISKIP_SEG_K];
    for &(source, owner) in owners {
        let warp = usize::from(owner);
        if warp >= UNISKIP_SEG_K {
            return Err(format!("source {source} owner {owner} is not a warp"));
        }
        let record = state
            .sources
            .get(usize::from(source))
            .ok_or_else(|| format!("owner names source {source}, past the source array"))?;
        let width = component_width(record.source_class);
        components[warp] += width;
        stores[warp] += match width {
            UNISKIP_COSET_E4_UNITS => 2,
            _ => 1,
        };
    }
    Ok((components, stores))
}

/// Reject a striping that misses a prologue row, names a warp that does not exist, or puts
/// a warp more than 4 components off the mean.
pub fn validate_owners(owners: &[(u16, u8)], state: &CacheArmState) -> Result<(), String> {
    let (components, _) = owner_sums(owners, state)?;
    let mut got: Vec<u16> = owners.iter().map(|&(source, _)| source).collect();
    let mut want: Vec<u16> = state.prologue().map(|row| row.source).collect();
    got.sort_unstable();
    want.sort_unstable();
    if got != want {
        return Err(format!(
            "{} owned sources do not match the {} prologue rows",
            got.len(),
            want.len()
        ));
    }
    let total: u32 = components.iter().sum();
    let k = UNISKIP_SEG_K as i64;
    for (warp, &sum) in components.iter().enumerate() {
        if (i64::from(sum) * k - i64::from(total)).abs() > 4 * k {
            return Err(format!(
                "warp {warp} holds {sum} components against a {total}/{UNISKIP_SEG_K} mean"
            ));
        }
    }
    Ok(())
}

/// Reject a plan that loses, duplicates or splits an atom, leaves a list empty, or lands
/// outside a 2x cost spread. Never panics — a bad plan is a wrong measurement, not a crash.
pub fn validate(plan: &SegPlan, original: &SynthProgram) -> Result<(), String> {
    if plan.list_offset[0] != 0 {
        return Err(format!("list_offset[0] is {}, not 0", plan.list_offset[0]));
    }
    if usize::from(plan.list_offset[UNISKIP_SEG_K]) != plan.program.len() {
        return Err(format!(
            "list_offset[{UNISKIP_SEG_K}] is {} against {} dealt records",
            plan.list_offset[UNISKIP_SEG_K],
            plan.program.len()
        ));
    }
    for k in 0..UNISKIP_SEG_K {
        if plan.list_offset[k] >= plan.list_offset[k + 1] {
            return Err(format!(
                "list {k} spans {}..{} and is empty or reversed",
                plan.list_offset[k],
                plan.list_offset[k + 1]
            ));
        }
    }

    let dealt = atoms(&plan.program, &original.sources)?;
    let source = atoms(&original.program, &original.sources)?;

    for k in 0..=UNISKIP_SEG_K {
        let offset = usize::from(plan.list_offset[k]);
        if offset != plan.program.len() && !dealt.iter().any(|atom| atom.pc == offset) {
            return Err(format!(
                "list_offset[{k}] = {offset} is inside an atom, not on its boundary"
            ));
        }
    }

    let mut got = atom_keys(&plan.program, &dealt);
    let mut expected = atom_keys(&original.program, &source);
    got.sort_unstable();
    expected.sort_unstable();
    if got != expected {
        return Err(format!(
            "dealt atoms are not the original {} atoms ({} dealt)",
            expected.len(),
            got.len()
        ));
    }

    let max = plan.predicted_cost.iter().copied().max().unwrap_or(0);
    let min = plan.predicted_cost.iter().copied().min().unwrap_or(0);
    if min == 0 {
        return Err("a list was predicted to cost nothing".to_string());
    }
    if max > 2 * min {
        return Err(format!(
            "predicted costs {:?} span more than 2x",
            plan.predicted_cost
        ));
    }
    Ok(())
}

/// The FNV-1a 64 fingerprint of a record stream, 16 lowercase hex.
pub fn program_hash(program: &[UniskipTerm]) -> String {
    let mut bytes = Vec::with_capacity(size_of_val(program));
    for term in program {
        for word in [term.term_class, term.coeff, term.source_a, term.source_b] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
    }
    format!("{:016x}", fnv1a64(&bytes))
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100_0000_01b3);
    }
    hash
}

/// One atom: its first record, how many records it spans, and its capture-blind cost.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Atom {
    pc: usize,
    records: usize,
    cost: u64,
}

/// Which cost a record pays for its coefficient, and whether it resolves operands at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    Plain,
    Header,
    Member,
}

fn atoms(program: &[UniskipTerm], sources: &[UniskipSourceRecord]) -> Result<Vec<Atom>, String> {
    let mut out = Vec::new();
    let mut pc = 0usize;
    while pc < program.len() {
        let head = program[pc];
        let group = head.term_class == UNISKIP_CLASS_GROUP_BF;
        let records = if group {
            1 + usize::from(head.source_a)
        } else {
            1
        };
        if pc + records > program.len() {
            return Err(format!(
                "atom at pc {pc} spans {records} records past the {}-record program",
                program.len()
            ));
        }
        let mut cost = record_cost(
            sources,
            head,
            if group { Role::Header } else { Role::Plain },
        )?;
        for member in &program[pc + 1..pc + records] {
            if member.term_class == UNISKIP_CLASS_GROUP_BF {
                return Err(format!("group at pc {pc} holds a nested group header"));
            }
            cost += record_cost(sources, *member, Role::Member)?;
        }
        out.push(Atom { pc, records, cost });
        pc += records;
    }
    Ok(out)
}

fn record_cost(
    sources: &[UniskipSourceRecord],
    term: UniskipTerm,
    role: Role,
) -> Result<u64, String> {
    let width = match role {
        Role::Header => 0,
        Role::Plain | Role::Member => {
            let a = operand_width(sources, term.source_a)?;
            let b = if term.source_b == term.source_a {
                0
            } else {
                operand_width(sources, term.source_b)?
            };
            a + b
        }
    };
    let product_mul = match term.term_class {
        UNISKIP_CLASS_PRODUCT_BF_BF => 1,
        UNISKIP_CLASS_PRODUCT_BF_E4 => 4,
        UNISKIP_CLASS_PRODUCT_E4_E4 => 8,
        _ => 0,
    };
    let apply = match role {
        Role::Plain | Role::Header => 4,
        Role::Member => {
            if term.coeff == UNISKIP_IMMEDIATE_ONE || term.coeff == UNISKIP_IMMEDIATE_NEG_ONE {
                1
            } else {
                2
            }
        }
    };
    Ok(width * SEG_CHAIN_COST + product_mul + apply)
}

fn operand_width(sources: &[UniskipSourceRecord], source: u16) -> Result<u64, String> {
    if source == UNISKIP_SOURCE_UNUSED {
        return Ok(0);
    }
    let record = sources
        .get(usize::from(source))
        .ok_or_else(|| format!("operand names source {source}, past the source array"))?;
    Ok(u64::from(component_width(record.source_class)))
}

/// An atom serialized as its COMPLETE record span — a record-level multiset would let a
/// member migrate between headers unnoticed.
fn atom_keys(program: &[UniskipTerm], atoms: &[Atom]) -> Vec<Vec<(u16, u16, u16, u16)>> {
    atoms
        .iter()
        .map(|atom| {
            program[atom.pc..atom.pc + atom.records]
                .iter()
                .map(|t| (t.term_class, t.coeff, t.source_a, t.source_b))
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::coset_cache::{plan_arm, CacheArm};
    use crate::synth::{generate, Census, TermOrder};
    use std::path::PathBuf;

    const ORDERS: [TermOrder; 2] = [TermOrder::Census, TermOrder::Locality];

    fn program(order: TermOrder) -> SynthProgram {
        let mut p = generate(0, Census::default()).unwrap();
        p.apply_term_order(order);
        p
    }

    /// The INDEPENDENT reference deal, written straight from the task brief's algorithm
    /// text: it re-derives atom spans, costs and the greedy assignment from scratch and
    /// shares nothing with the implementation above.
    fn reference_deal(p: &SynthProgram) -> ([u16; UNISKIP_SEG_K + 1], Vec<UniskipTerm>, [u64; 4]) {
        let mut spans: Vec<(usize, usize, u64)> = Vec::new();
        let mut pc = 0usize;
        while pc < p.program.len() {
            let head = p.program[pc];
            let grouped = head.term_class == UNISKIP_CLASS_GROUP_BF;
            let span = if grouped {
                1 + head.source_a as usize
            } else {
                1
            };
            let mut cost = 0u64;
            for i in 0..span {
                let r = p.program[pc + i];
                let is_header = grouped && i == 0;
                let is_member = grouped && i > 0;
                let mut c = 0u64;
                if !is_header {
                    for (which, source) in [(0u8, r.source_a), (1u8, r.source_b)] {
                        if source == UNISKIP_SOURCE_UNUSED {
                            continue;
                        }
                        if which == 1 && source == r.source_a {
                            continue;
                        }
                        let e4 = p.sources[source as usize].source_class == UNISKIP_SRC_E4_GLOBAL;
                        c += 7 * if e4 { 4 } else { 1 };
                    }
                }
                c += match r.term_class {
                    UNISKIP_CLASS_PRODUCT_BF_BF => 1,
                    UNISKIP_CLASS_PRODUCT_BF_E4 => 4,
                    UNISKIP_CLASS_PRODUCT_E4_E4 => 8,
                    _ => 0,
                };
                c += if is_member {
                    if r.coeff == UNISKIP_IMMEDIATE_ONE || r.coeff == UNISKIP_IMMEDIATE_NEG_ONE {
                        1
                    } else {
                        2
                    }
                } else {
                    4
                };
                cost += c;
            }
            spans.push((pc, span, cost));
            pc += span;
        }

        let mut load = [0u64; 4];
        let mut lists: Vec<Vec<(usize, usize)>> = vec![Vec::new(); 4];
        for (pc, span, cost) in spans {
            let mut best = 0usize;
            for w in 1..4 {
                if load[w] < load[best] {
                    best = w;
                }
            }
            load[best] += cost;
            lists[best].push((pc, span));
        }

        let mut records = Vec::new();
        let mut offset = [0u16; UNISKIP_SEG_K + 1];
        for (i, list) in lists.iter().enumerate() {
            for &(pc, span) in list {
                records.extend_from_slice(&p.program[pc..pc + span]);
            }
            offset[i + 1] = records.len() as u16;
        }
        (offset, records, load)
    }

    /// Layer (a) of the oracle: the dealer equals a reference derived independently of it.
    #[test]
    fn cpu_seg_deal_covers_default_census() {
        for order in ORDERS {
            let p = program(order);
            let plan = deal(&p).unwrap();
            let (offset, records, cost) = reference_deal(&p);
            assert_eq!(plan.list_offset, offset, "list_offset, {order:?}");
            assert_eq!(plan.program, records, "dealt program, {order:?}");
            assert_eq!(plan.predicted_cost, cost, "predicted cost, {order:?}");
            assert_eq!(plan.program.len(), p.program.len(), "{order:?}");
            validate(&plan, &p).unwrap();
        }
    }

    /// A group header and every one of its members land in ONE list, contiguously.
    #[test]
    fn cpu_seg_atoms_never_split() {
        for order in ORDERS {
            let p = program(order);
            let plan = deal(&p).unwrap();
            let mut groups = 0;
            for k in 0..UNISKIP_SEG_K {
                let (lo, hi) = (
                    usize::from(plan.list_offset[k]),
                    usize::from(plan.list_offset[k + 1]),
                );
                let mut pc = lo;
                while pc < hi {
                    let head = plan.program[pc];
                    let span = if head.term_class == UNISKIP_CLASS_GROUP_BF {
                        groups += 1;
                        1 + usize::from(head.source_a)
                    } else {
                        1
                    };
                    assert!(pc + span <= hi, "atom at {pc} crosses list {k}'s end {hi}");
                    pc += span;
                }
                assert_eq!(pc, hi, "list {k} does not tile with whole atoms, {order:?}");
            }
            assert_eq!(groups, p.census.groups, "every group survives, {order:?}");
        }
    }

    /// Greedy least-loaded bounds the spread by one atom's cost; the 2x ratio the
    /// validator pins is far looser than what the default census actually reaches.
    #[test]
    fn cpu_seg_lists_balanced_both_orders() {
        for order in ORDERS {
            let p = program(order);
            let plan = deal(&p).unwrap();
            let max = plan.predicted_cost.iter().copied().max().unwrap();
            let min = plan.predicted_cost.iter().copied().min().unwrap();
            let widest = atoms(&p.program, &p.sources)
                .unwrap()
                .iter()
                .map(|a| a.cost)
                .max()
                .unwrap();
            assert!(max <= 2 * min, "{:?}, {order:?}", plan.predicted_cost);
            assert!(
                max - min <= widest,
                "spread {} over the widest atom {widest}, {order:?}",
                max - min
            );
        }
    }

    /// hot16 admits 12 `bf` and 4 `e4` sources: 28 components and 20 stores, which stripe
    /// to exactly 7 components and 5 store instructions per warp.
    #[test]
    fn cpu_seg_hot16_owner_balance_is_7_components() {
        let p = program(TermOrder::Census);
        let state = plan_arm(&p, CacheArm::Hot16).unwrap();
        let owners = stripe_prologue(&state);
        assert_eq!(owners.len(), 16);
        assert!(owners.iter().all(|&(_, w)| usize::from(w) < UNISKIP_SEG_K));
        let (components, stores) = owner_sums(&owners, &state).unwrap();
        assert_eq!(components, [7; UNISKIP_SEG_K]);
        assert_eq!(stores, [5; UNISKIP_SEG_K]);
        validate_owners(&owners, &state).unwrap();
    }

    #[test]
    fn cpu_seg_validator_rejects_split_atom() {
        let p = program(TermOrder::Census);
        let plan = deal(&p).unwrap();
        let mut split = None;
        for k in 1..UNISKIP_SEG_K {
            let (lo, hi) = (
                usize::from(plan.list_offset[k - 1]),
                usize::from(plan.list_offset[k + 1]),
            );
            let mut pc = lo;
            while pc < hi {
                let head = plan.program[pc];
                let span = if head.term_class == UNISKIP_CLASS_GROUP_BF {
                    1 + usize::from(head.source_a)
                } else {
                    1
                };
                if span > 1 && pc > lo && pc + 1 < hi {
                    split = Some((k, pc + 1));
                    break;
                }
                pc += span;
            }
            if split.is_some() {
                break;
            }
        }
        let (k, interior) = split.expect("the default census deals at least one group");
        let mut bad = plan.clone();
        bad.list_offset[k] = interior as u16;
        assert!(validate(&bad, &p).is_err());
        assert!(validate(&plan, &p).is_ok());
    }

    #[test]
    fn cpu_seg_validator_rejects_missing_record() {
        let p = program(TermOrder::Census);
        let plan = deal(&p).unwrap();
        let mut bad = plan.clone();
        bad.program.pop().unwrap();
        bad.list_offset[UNISKIP_SEG_K] -= 1;
        assert!(validate(&bad, &p).is_err());
    }

    /// The drift key must stay a standard algorithm both this crate and the emitter can
    /// compute, so the three published FNV-1a 64 vectors are pinned here.
    #[test]
    fn cpu_seg_program_hash_pins_fnv1a64() {
        assert_eq!(fnv1a64(b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a64(b"a"), 0xaf63_dc4c_8601_ec8c);
        assert_eq!(fnv1a64(b"foobar"), 0x8594_4171_f739_67e8);
        let term = UniskipTerm {
            term_class: 1,
            coeff: 2,
            source_a: 3,
            source_b: 4,
        };
        assert_eq!(
            program_hash(&[term]),
            format!("{:016x}", fnv1a64(&[1, 0, 2, 0, 3, 0, 4, 0]))
        );
    }

    fn oracle_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tools/r7_fixtures/seg_oracle.json")
    }

    fn numbers<T: std::fmt::Display>(values: impl IntoIterator<Item = T>) -> String {
        values
            .into_iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Layer (b) of the oracle: the committed fixture, rendered stable-ordered so a diff
    /// reads as a change of plan rather than a reshuffle.
    fn oracle_json() -> String {
        let census = Census::default();
        let mut out = String::new();
        out.push_str("{\n");
        out.push_str("  \"kind\": \"v3 R7 seg dealer oracle\",\n");
        out.push_str("  \"regenerate\": \"GPU_GKR_UNISKIP_BENCH_REGEN_SEG_ORACLE=1 cargo test -p gpu_gkr_uniskip_bench --lib --release cpu_seg_oracle 9>&-\",\n");
        out.push_str(&format!("  \"seg_k\": {UNISKIP_SEG_K},\n"));
        out.push_str("  \"census\": {\n");
        out.push_str("    \"seed\": 0,\n");
        out.push_str(&format!("    \"sources\": {},\n", census.sources));
        out.push_str(&format!(
            "    \"semantic_terms\": {},\n",
            census.semantic_terms
        ));
        out.push_str(&format!("    \"groups\": {},\n", census.groups));
        out.push_str(&format!(
            "    \"grouped_atoms\": {}\n",
            census.grouped_atoms
        ));
        out.push_str("  },\n");
        out.push_str("  \"program_hash_algo\": \"fnv1a64\",\n");
        out.push_str("  \"program_hash_input\": \"per record: term_class, coeff, source_a, source_b as u16 little-endian\",\n");
        out.push_str("  \"owner_arm\": \"hot16\",\n");
        out.push_str("  \"orders\": [\n");
        for (i, order) in ORDERS.iter().enumerate() {
            let p = program(*order);
            let plan = deal(&p).unwrap();
            let state = plan_arm(&p, CacheArm::Hot16).unwrap();
            let owners = stripe_prologue(&state);
            let (components, stores) = owner_sums(&owners, &state).unwrap();
            out.push_str("    {\n");
            out.push_str(&format!("      \"term_order\": \"{}\",\n", order.as_str()));
            out.push_str(&format!("      \"records\": {},\n", plan.program.len()));
            out.push_str(&format!(
                "      \"atoms\": {},\n",
                atoms(&plan.program, &p.sources).unwrap().len()
            ));
            out.push_str(&format!(
                "      \"list_offset\": [{}],\n",
                numbers(plan.list_offset)
            ));
            out.push_str(&format!(
                "      \"predicted_cost\": [{}],\n",
                numbers(plan.predicted_cost)
            ));
            out.push_str(&format!(
                "      \"program_hash\": \"{}\",\n",
                program_hash(&plan.program)
            ));
            out.push_str(&format!(
                "      \"owner_components\": [{}],\n",
                numbers(components)
            ));
            out.push_str(&format!("      \"owner_stores\": [{}]\n", numbers(stores)));
            out.push_str(if i + 1 == ORDERS.len() {
                "    }\n"
            } else {
                "    },\n"
            });
        }
        out.push_str("  ]\n");
        out.push_str("}\n");
        out
    }

    #[test]
    fn cpu_seg_oracle() {
        const REGEN: &str = "GPU_GKR_UNISKIP_BENCH_REGEN_SEG_ORACLE";
        let path = oracle_path();
        let want = oracle_json();
        if std::env::var(REGEN).is_ok_and(|v| v == "1") {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, &want).unwrap();
            return;
        }
        let got = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{}: {e}; regenerate with {REGEN}=1", path.display()));
        assert_eq!(got, want, "seg oracle drift; regenerate with {REGEN}=1");
    }
}
