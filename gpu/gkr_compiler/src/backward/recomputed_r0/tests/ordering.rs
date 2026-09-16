//! Ordering may move complete units only; their member order and source-lane offsets are exact.
use super::super::super::window::reorder_recomputed_window_boundaries;
use super::*;
use std::collections::HashMap;
const GROUP_BF: u16 = 6;
const GROUP_E4: u16 = 7;
fn rec(p: &WindowProgram, pc: usize) -> (u16, u16, u16, u16) {
    let w = &p.words;
    (w[4 * pc], w[4 * pc + 1], w[4 * pc + 2], w[4 * pc + 3])
}

/// One whole unit of the emitted program: a BF/E4 group head with all its members, or a single record.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Unit {
    pub section: u8,
    pub first: usize,
    pub records: usize,
}

/// Walk the four sections into whole units; errors on any structural inconsistency.
fn units(p: &WindowProgram) -> Result<Vec<Unit>, String> {
    if p.words.len() % 4 != 0 {
        return Err(format!("words.len {} not a multiple of 4", p.words.len()));
    }
    let total = p.words.len() / 4;
    let s: Vec<usize> = p.sections[..4].iter().map(|&v| v as usize).collect();
    if !(s[0] <= s[1] && s[1] <= s[2] && s[2] <= s[3]) || s[3] != total {
        return Err(format!(
            "sections {:?} inconsistent with {} records",
            s, total
        ));
    }
    let mut out = Vec::new();
    let mut pc = 0usize;
    while pc < s[0] {
        let (op, _, a, _) = rec(p, pc);
        let n = if op == GROUP_BF { 1 + a as usize } else { 1 };
        if pc + n > s[0] {
            return Err(format!("BF group at {pc} overruns section 0"));
        }
        for m in 1..n {
            let mop = rec(p, pc + m).0;
            if matches!(mop, GROUP_BF | GROUP_E4) {
                return Err(format!("nested head at {}", pc + m));
            }
        }
        out.push(Unit {
            section: 0,
            first: pc,
            records: n,
        });
        pc += n;
    }
    while pc < s[1] {
        if matches!(rec(p, pc).0, GROUP_BF | GROUP_E4) {
            return Err(format!("head in LE4 at {pc}"));
        }
        out.push(Unit {
            section: 1,
            first: pc,
            records: 1,
        });
        pc += 1;
    }
    while pc < s[2] {
        if matches!(rec(p, pc).0, GROUP_BF | GROUP_E4) {
            return Err(format!("head in SE4 at {pc}"));
        }
        out.push(Unit {
            section: 2,
            first: pc,
            records: 1,
        });
        pc += 1;
    }
    while pc < s[3] {
        if rec(p, pc).0 != GROUP_E4 {
            return Err(format!("non-head at PE4 {pc}"));
        }
        if pc + 3 > s[3] {
            return Err(format!("E4 group at {pc} overruns section 3"));
        }
        for m in 1..3 {
            if matches!(rec(p, pc + m).0, GROUP_BF | GROUP_E4) {
                return Err(format!("nested E4 head at {}", pc + m));
            }
        }
        out.push(Unit {
            section: 3,
            first: pc,
            records: 3,
        });
        pc += 3;
    }
    Ok(out)
}

/// Canonical key of a unit: section, its words, and its lanes as (word offset relative to the unit, source slot).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct UnitKey {
    pub section: u8,
    pub words: Vec<u16>,
    pub lanes: Vec<(u32, u16)>,
}

fn unit_keys(p: &WindowProgram, us: &[Unit]) -> Result<Vec<UnitKey>, String> {
    let mut by_word: HashMap<u32, u16> = HashMap::new();
    for l in &p.source_lanes {
        if l.word as usize >= p.words.len() {
            return Err(format!("lane word {} out of range", l.word));
        }
        if l.word % 4 < 2 {
            return Err(format!("lane word {} is not an operand word", l.word));
        }
        if by_word.insert(l.word, l.source).is_some() {
            return Err(format!("duplicate lane word {}", l.word));
        }
        if l.source as usize >= p.source_slots.len() {
            return Err(format!("lane source {} out of range", l.source));
        }
    }
    let mut keys = Vec::with_capacity(us.len());
    for u in us {
        let lo = 4 * u.first as u32;
        let hi = 4 * (u.first + u.records) as u32;
        let mut lanes: Vec<(u32, u16)> = by_word
            .iter()
            .filter(|(w, _)| **w >= lo && **w < hi)
            .map(|(w, s)| (*w - lo, *s))
            .collect();
        lanes.sort();
        keys.push(UnitKey {
            section: u.section,
            words: p.words[lo as usize..hi as usize].to_vec(),
            lanes,
        });
    }
    Ok(keys)
}

/// Every invariant a boundary permutation must keep. Empty vector = pass.
fn check(before: &WindowProgram, after: &WindowProgram) -> Vec<String> {
    let mut e = Vec::new();
    if before.layer != after.layer {
        e.push("layer differs".into());
    }
    if before.sections != after.sections {
        e.push(format!(
            "sections differ {:?} vs {:?}",
            &before.sections[..5],
            &after.sections[..5]
        ));
    }
    if before.shape != after.shape {
        e.push("shape differs".into());
    }
    if before.source_slots != after.source_slots {
        e.push("source_slots differ".into());
    }
    if before.windows != after.windows {
        e.push("windows differ".into());
    }
    if before.immediates != after.immediates {
        e.push("immediates differ".into());
    }
    if before.coefficient_plans != after.coefficient_plans {
        e.push("coefficient_plans differ".into());
    }
    if before.words.len() != after.words.len() {
        e.push(format!(
            "words.len {} vs {}",
            before.words.len(),
            after.words.len()
        ));
    }
    if before.source_lanes.len() != after.source_lanes.len() {
        e.push(format!(
            "source_lanes.len {} vs {}",
            before.source_lanes.len(),
            after.source_lanes.len()
        ));
    }
    let (ub, ua) = match (units(before), units(after)) {
        (Ok(a), Ok(b)) => (a, b),
        (Err(x), _) => {
            e.push(format!("before units: {x}"));
            return e;
        }
        (_, Err(x)) => {
            e.push(format!("after units: {x}"));
            return e;
        }
    };
    let (kb, ka) = match (unit_keys(before, &ub), unit_keys(after, &ua)) {
        (Ok(a), Ok(b)) => (a, b),
        (Err(x), _) => {
            e.push(format!("before lanes: {x}"));
            return e;
        }
        (_, Err(x)) => {
            e.push(format!("after lanes: {x}"));
            return e;
        }
    };
    for sec in 0..4u8 {
        let mut a: Vec<&UnitKey> = kb.iter().filter(|k| k.section == sec).collect();
        let mut b: Vec<&UnitKey> = ka.iter().filter(|k| k.section == sec).collect();
        if a.len() != b.len() {
            e.push(format!("section {sec}: {} vs {} units", a.len(), b.len()));
            continue;
        }
        a.sort();
        b.sort();
        if a != b {
            let missing = a.iter().filter(|k| !b.contains(k)).count();
            e.push(format!("section {sec}: unit multiset differs ({missing} units of the original not found after)"));
        }
    }
    e
}

#[test]
fn cpu_boundary_order_preserves_whole_units_corpus() {
    let mut coordinates = 0;
    let mut expected_coordinates = 0;
    let mut changed = 0;
    for name in crate::backward::corpus_tests::CORPUS {
        let dag = super::load_dag(name);
        expected_coordinates += 2 * dag.layers.len();
        for tails in [false, true] {
            for layer in compile_lowering(&dag, tails).unwrap() {
                let before = layer.window;
                let mut after = before.clone();
                reorder_recomputed_window_boundaries(&mut after);
                let moved =
                    before.words != after.words || before.source_lanes != after.source_lanes;
                assert!(
                    check(&before, &after).is_empty(),
                    "{name} L{} tails={tails}: {:?}",
                    before.layer,
                    check(&before, &after)
                );
                if !after.words.is_empty() {
                    let mut broken = after.clone();
                    broken.words[1] ^= 1;
                    assert!(
                        !check(&before, &broken).is_empty(),
                        "missed factor corruption"
                    );
                }
                if !after.source_lanes.is_empty() {
                    let mut broken = after.clone();
                    broken.source_lanes.pop();
                    assert!(
                        !check(&before, &broken).is_empty(),
                        "missed missing operand binding"
                    );
                }
                let mut broken = after.clone();
                broken.sections[0] += 1;
                assert!(
                    !check(&before, &broken).is_empty(),
                    "missed section corruption"
                );
                coordinates += 1;
                changed += usize::from(moved);
            }
        }
    }
    assert!(expected_coordinates > 0);
    assert_eq!(coordinates, expected_coordinates);
    assert!(changed > 0, "the corpus never exercised a permutation");
}
