//! Exact corpus oracle for the whole-unit source partition planner. The oracle decodes units,
//! physical sources and components independently of the planner's own routines.
use super::super::{
    validate_window_coefficient_ids, validate_window_source_lanes, WindowProgram, WindowSourceLane,
};
use super::{Partitioner, R0PartitionPlan};

fn partition_r0_window(
    program: &WindowProgram,
    parts: usize,
) -> Result<R0PartitionPlan, super::WindowLoweringError> {
    Partitioner::new(program)?.plan(parts)
}
use crate::backward::common::Bf;
use crate::backward::r0::{compile_r0, R0WindowProgram};
use gkr_eval_ir::FieldKind;
use std::collections::{BTreeMap, BTreeSet, HashMap};

const GROUP_BF: u16 = 6;
const GROUP_E4: u16 = 7;
const PARTS: [usize; 5] = [1, 2, 4, 8, 16];

fn load_dag(name: &str) -> gkr_eval_ir::DagCircuit {
    let directory =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let artifact: cs::gkr_compiler::GKRCircuitArtifact<Bf> =
        serde_json::from_slice(&std::fs::read(directory.join(name)).unwrap()).unwrap();
    gkr_eval_ir::lower_dag(&artifact).unwrap()
}

fn selected_programs(dag: &gkr_eval_ir::DagCircuit) -> Vec<R0WindowProgram> {
    compile_r0(dag).unwrap()
}

fn rec(p: &WindowProgram, pc: usize) -> (u16, u16, u16, u16) {
    let w = &p.words;
    (w[4 * pc], w[4 * pc + 1], w[4 * pc + 2], w[4 * pc + 3])
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Unit {
    section: u8,
    first: usize,
    records: usize,
}

fn units(p: &WindowProgram) -> Result<Vec<Unit>, String> {
    if !p.words.len().is_multiple_of(4) {
        return Err(format!("words.len {} not a multiple of 4", p.words.len()));
    }
    let total = p.words.len() / 4;
    let s: Vec<usize> = p.sections[..4].iter().map(|&v| v as usize).collect();
    if !(s[0] <= s[1] && s[1] <= s[2] && s[2] <= s[3]) || s[3] != total {
        return Err(format!("sections {s:?} inconsistent with {total} records"));
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
            if matches!(rec(p, pc + m).0, GROUP_BF | GROUP_E4) {
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
    for section in 1..3u8 {
        while pc < s[section as usize] {
            if matches!(rec(p, pc).0, GROUP_BF | GROUP_E4) {
                return Err(format!("head in section {section} at {pc}"));
            }
            out.push(Unit {
                section,
                first: pc,
                records: 1,
            });
            pc += 1;
        }
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

/// Canonical key of a unit: section, words, lanes as (unit-relative word, slot).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct UnitKey {
    section: u8,
    words: Vec<u16>,
    lanes: Vec<(u32, u16)>,
}

fn lanes_by_word(p: &WindowProgram) -> Result<HashMap<u32, u16>, String> {
    let mut by_word = HashMap::new();
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
    Ok(by_word)
}

fn unit_keys(p: &WindowProgram, us: &[Unit]) -> Result<Vec<UnitKey>, String> {
    let by_word = lanes_by_word(p)?;
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

/// Physical source identity: (window family, absolute column, bytes per corner value).
type Physical = (String, usize, usize);

/// Physical identity per slot; procedural slots are `None`.
fn physical_slots(p: &WindowProgram) -> Result<Vec<Option<Physical>>, String> {
    let mut out = Vec::with_capacity(p.source_slots.len());
    for &lane in &p.source_slots {
        let window = p
            .windows
            .get(usize::from(lane >> 7))
            .ok_or_else(|| format!("slot {lane:#x} names an absent window"))?;
        if window.procedural_kind().is_some() {
            out.push(None);
            continue;
        }
        let width = match window.backing_field() {
            FieldKind::Base => 4,
            FieldKind::Ext => 16,
        };
        out.push(Some((
            format!("{:?}", window.family),
            window.first_column + usize::from(lane & 0x7f),
            width,
        )));
    }
    Ok(out)
}

/// Physical sources per unit (procedural excluded), rejecting one column bound at two widths.
fn unit_sources(p: &WindowProgram, us: &[Unit]) -> Result<Vec<BTreeSet<Physical>>, String> {
    let by_word = lanes_by_word(p)?;
    let physical = physical_slots(p)?;
    let mut widths: BTreeMap<(String, usize), usize> = BTreeMap::new();
    for (family, column, width) in physical.iter().flatten() {
        if *widths.entry((family.clone(), *column)).or_insert(*width) != *width {
            return Err(format!("{family} column {column} bound at two widths"));
        }
    }
    Ok(us
        .iter()
        .map(|u| {
            (4 * u.first..4 * (u.first + u.records))
                .filter_map(|word| by_word.get(&(word as u32)))
                .filter_map(|&slot| physical[usize::from(slot)].clone())
                .collect()
        })
        .collect())
}

fn bytes(sources: &BTreeSet<Physical>) -> usize {
    sources.iter().map(|(_, _, width)| 32 * 8 * width).sum()
}

fn union(sets: &[BTreeSet<Physical>]) -> BTreeSet<Physical> {
    sets.iter().flatten().cloned().collect()
}

/// Number of connected components of units over shared physical sources.
fn components(sources: &[BTreeSet<Physical>]) -> usize {
    let mut parent: Vec<usize> = (0..sources.len()).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            x = parent[x];
        }
        x
    }
    let mut owner: BTreeMap<&Physical, usize> = BTreeMap::new();
    for (index, set) in sources.iter().enumerate() {
        for source in set {
            if let Some(&other) = owner.get(source) {
                let (a, b) = (find(&mut parent, index), find(&mut parent, other));
                if a != b {
                    parent[a] = b;
                }
            } else {
                owner.insert(source, index);
            }
        }
    }
    (0..sources.len())
        .filter(|&index| find(&mut parent, index) == index)
        .count()
}

fn is_subsequence(part: &[&UnitKey], whole: &[&UnitKey]) -> bool {
    let mut cursor = 0;
    for key in part {
        while cursor < whole.len() && whole[cursor] != *key {
            cursor += 1;
        }
        if cursor == whole.len() {
            return false;
        }
        cursor += 1;
    }
    true
}

/// Every invariant a partition plan must keep against its input. Empty vector = pass.
fn check(before: &WindowProgram, plan: &R0PartitionPlan, requested: usize) -> Vec<String> {
    let mut e = Vec::new();
    let parts = &plan.parts;
    if parts.is_empty() {
        return vec!["no parts".into()];
    }
    if parts.len() > requested {
        e.push(format!("{} parts for {requested} requested", parts.len()));
    }
    if parts.len() != plan.source_bytes_per_tile.len() {
        e.push("byte vector length differs from parts".into());
    }
    if requested == 1 && parts[0] != *before {
        e.push("K=1 part is not the original program".into());
    }
    let (ub, kb, sb) = match units(before)
        .and_then(|u| Ok((unit_keys(before, &u)?, unit_sources(before, &u)?, u)))
    {
        Ok((k, s, u)) => (u, k, s),
        Err(x) => return vec![format!("before: {x}")],
    };
    if parts.len() != requested.min(components(&sb)).max(1) {
        e.push(format!(
            "{} parts, expected min({requested}, {} components)",
            parts.len(),
            components(&sb)
        ));
    }
    let mut all_keys: Vec<UnitKey> = Vec::new();
    let mut part_sources: Vec<BTreeSet<Physical>> = Vec::new();
    for (index, part) in parts.iter().enumerate() {
        if part.layer != before.layer
            || part.shape != before.shape
            || part.source_slots != before.source_slots
            || part.windows != before.windows
            || part.immediates != before.immediates
            || part.coefficient_plans != before.coefficient_plans
        {
            e.push(format!("part {index}: metadata differs"));
        }
        if let Err(x) = validate_window_coefficient_ids(part) {
            e.push(format!("part {index}: coefficient validator: {x:?}"));
        }
        if let Err(x) = validate_window_source_lanes(part) {
            e.push(format!("part {index}: source lane validator: {x:?}"));
        }
        let (u, k, s) = match units(part)
            .and_then(|u| Ok((unit_keys(part, &u)?, unit_sources(part, &u)?, u)))
        {
            Ok((k, s, u)) => (u, k, s),
            Err(x) => {
                e.push(format!("part {index}: {x}"));
                continue;
            }
        };
        if u.is_empty() && !ub.is_empty() {
            e.push(format!("part {index}: empty"));
        }
        for section in 0..4u8 {
            let mine: Vec<&UnitKey> = k.iter().filter(|k| k.section == section).collect();
            let whole: Vec<&UnitKey> = kb.iter().filter(|k| k.section == section).collect();
            if !is_subsequence(&mine, &whole) {
                e.push(format!(
                    "part {index}: section {section} order not preserved"
                ));
            }
        }
        let sources = union(&s);
        if plan.source_bytes_per_tile.get(index) != Some(&bytes(&sources)) {
            e.push(format!(
                "part {index}: reported bytes differ from footprint"
            ));
        }
        for (other, previous) in part_sources.iter().enumerate() {
            if !previous.is_disjoint(&sources) {
                e.push(format!("parts {other} and {index} share physical sources"));
            }
        }
        part_sources.push(sources);
        all_keys.extend(k);
    }
    let mut expected = kb.clone();
    expected.sort();
    all_keys.sort();
    if expected != all_keys {
        e.push("unit multiset across parts differs from the original".into());
    }
    if plan.source_bytes_per_tile.iter().sum::<usize>() != bytes(&union(&sb)) {
        e.push("summed part bytes differ from the original footprint".into());
    }
    e
}

#[test]
fn cpu_partition_plans_are_exact_corpus() {
    let mut programs = 0;
    let mut coordinates = 0;
    let mut split = 0;
    let mut procedural_cases = 0;
    for name in crate::backward::corpus_tests::CORPUS {
        let dag = load_dag(name);
        for selected in selected_programs(&dag) {
            let before = &selected.window;
            programs += 1;
            let us = units(before).unwrap();
            let sources = unit_sources(before, &us).unwrap();
            let physical = physical_slots(before).unwrap();
            procedural_cases += usize::from(physical.iter().any(|p| p.is_none()));
            let real_components = components(&sources);
            for &k in &PARTS {
                let plan = partition_r0_window(before, k).unwrap_or_else(|error| {
                    panic!("{name} L{} K={k}: {error:?}", selected.window.layer)
                });
                let again = partition_r0_window(before, k).unwrap();
                assert_eq!(
                    plan.parts, again.parts,
                    "{name} L{} K={k} nondeterministic",
                    selected.window.layer
                );
                assert_eq!(plan.source_bytes_per_tile, again.source_bytes_per_tile);
                let errors = check(before, &plan, k);
                assert!(
                    errors.is_empty(),
                    "{name} L{} K={k}: {errors:?}",
                    selected.window.layer
                );
                assert_eq!(plan.parts.len(), k.min(real_components).max(1));
                assert_eq!(
                    plan.parts.iter().map(|p| p.words.len()).sum::<usize>(),
                    before.words.len(),
                    "{name} L{} K={k}: records added or dropped (no seed record may be inserted)",
                    selected.window.layer
                );
                if k == 1 {
                    assert_eq!(
                        plan.parts[0], *before,
                        "{name} L{}: K=1 must clone",
                        selected.window.layer
                    );
                }
                split += usize::from(plan.parts.len() > 1);
                coordinates += 1;
            }
        }
    }
    assert_eq!(programs, 56, "the selected corpus is 56 programs");
    assert_eq!(coordinates, 56 * PARTS.len());
    assert!(split > 0, "the corpus never split a program");
    assert!(
        procedural_cases > 0,
        "no selected program carries a procedural slot"
    );
}

#[test]
fn cpu_partition_rejects_malformed_input() {
    let dag = load_dag(crate::backward::corpus_tests::CORPUS[0]);
    let programs = selected_programs(&dag);
    let base = programs
        .iter()
        .map(|p| &p.window)
        .find(|p| {
            p.words.len() >= 12 && !p.source_lanes.is_empty() && p.sections[3] > p.sections[2]
        })
        .expect("a program with lanes and a pair section");
    assert!(partition_r0_window(base, 0).is_err(), "zero parts");
    let mut broken = base.clone();
    broken.words.push(0);
    assert!(partition_r0_window(&broken, 2).is_err(), "ragged words");
    let mut broken = base.clone();
    broken.sections[0] = broken.sections[3] + 1;
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "non-monotone sections"
    );
    let mut broken = base.clone();
    broken.sections[3] -= 1;
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "records after the last section"
    );
    let mut broken = base.clone();
    broken.source_lanes[0].word = broken.words.len() as u32;
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "lane word out of range"
    );
    let mut broken = base.clone();
    broken.source_lanes[0].word &= !3;
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "lane on a non-operand word"
    );
    let mut broken = base.clone();
    let duplicate = broken.source_lanes[0];
    broken.source_lanes.push(duplicate);
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "duplicate lane word"
    );
    let mut broken = base.clone();
    broken.source_lanes[0].source = broken.source_slots.len() as u16;
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "lane names an absent slot"
    );
    let mut broken = base.clone();
    broken.source_slots.push(u16::MAX);
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "slot names an absent window"
    );
    let mut broken = base.clone();
    let head = 4 * broken.sections[2] as usize;
    broken.words[head] = 3;
    assert!(
        partition_r0_window(&broken, 2).is_err(),
        "pair section without a head"
    );
    let mut broken = base.clone();
    broken.words[head + 4] = GROUP_E4;
    assert!(partition_r0_window(&broken, 2).is_err(), "nested pair head");
    // Fast paths reject malformed input like the split path does.
    let mut broken = base.clone();
    broken.words.push(0);
    assert!(partition_r0_window(&broken, 1).is_err(), "K=1 ragged words");
}

#[test]
fn cpu_partition_empty_program_is_one_part() {
    let dag = load_dag(crate::backward::corpus_tests::CORPUS[0]);
    let mut empty = selected_programs(&dag)[0].window.clone();
    empty.words.clear();
    empty.source_lanes.clear();
    empty.sections[..4].copy_from_slice(&[0; 4]);
    for k in PARTS {
        let plan = partition_r0_window(&empty, k).unwrap();
        assert_eq!(plan.parts, vec![empty.clone()]);
        assert_eq!(plan.source_bytes_per_tile, vec![0]);
    }
}

/// A lane of `before` inside a unit that the K=8 plan placed in part `part` and no other,
/// accepted by `accept`; returned with the unit's index in `before`.
fn lane_in_part(
    before: &WindowProgram,
    plan: &R0PartitionPlan,
    part: usize,
    accept: impl Fn(&WindowSourceLane) -> bool,
) -> Option<(usize, WindowSourceLane)> {
    let ub = units(before).unwrap();
    let kb = unit_keys(before, &ub).unwrap();
    let keys: Vec<BTreeSet<UnitKey>> = plan
        .parts
        .iter()
        .map(|part| {
            unit_keys(part, &units(part).unwrap())
                .unwrap()
                .into_iter()
                .collect()
        })
        .collect();
    ub.iter().enumerate().find_map(|(index, unit)| {
        let only_here = keys
            .iter()
            .enumerate()
            .all(|(other, set)| set.contains(&kb[index]) == (other == part));
        if !only_here {
            return None;
        }
        let range = 4 * unit.first..4 * (unit.first + unit.records);
        before
            .source_lanes
            .iter()
            .copied()
            .find(|lane| range.contains(&(lane.word as usize)) && accept(lane))
            .map(|lane| (index, lane))
    })
}

/// Rebind `lane` in `program` to `slot`; the operand word carries the slot's encoded column.
fn rebind(program: &mut WindowProgram, lane: WindowSourceLane, slot: u16) {
    for candidate in &mut program.source_lanes {
        if candidate.word == lane.word {
            candidate.source = slot;
        }
    }
    program.words[lane.word as usize] = program.source_slots[usize::from(slot)];
}

fn clone_plan(plan: &R0PartitionPlan) -> R0PartitionPlan {
    R0PartitionPlan {
        parts: plan.parts.clone(),
        source_bytes_per_tile: plan.source_bytes_per_tile.clone(),
    }
}

/// Two slots bound to one physical column link their units and count the column once; a plan
/// built from slot identity instead of physical identity is rejected by the oracle.
#[test]
fn cpu_partition_aliases_link_by_physical_column() {
    let mut exercised = 0;
    for name in crate::backward::corpus_tests::CORPUS {
        let dag = load_dag(name);
        for selected in selected_programs(&dag) {
            let before = &selected.window;
            let plan = partition_r0_window(before, 8).unwrap();
            if plan.parts.len() < 2 {
                continue;
            }
            let physical = physical_slots(before).unwrap();
            let width = |slot: u16| physical[usize::from(slot)].as_ref().map(|p| p.2);
            let Some((target_index, target)) =
                lane_in_part(before, &plan, 1, |lane| width(lane.source).is_some())
            else {
                continue;
            };
            let Some((_, donor)) = lane_in_part(before, &plan, 0, |lane| {
                width(lane.source).is_some() && width(lane.source) == width(target.source)
            }) else {
                continue;
            };
            let mut aliased = before.clone();
            let alias = aliased.source_slots.len() as u16;
            aliased
                .source_slots
                .push(before.source_slots[usize::from(donor.source)]);
            rebind(&mut aliased, target, alias);
            if validate_window_source_lanes(&aliased).is_err() {
                continue;
            }
            let aliased_plan = partition_r0_window(&aliased, 8).unwrap();
            let errors = check(&aliased, &aliased_plan, 8);
            assert!(
                errors.is_empty(),
                "{name} L{}: {errors:?}",
                selected.window.layer
            );
            let alias_part = aliased_plan
                .parts
                .iter()
                .position(|part| part.source_lanes.iter().any(|lane| lane.source == alias))
                .unwrap();
            assert!(
                aliased_plan.parts[alias_part]
                    .source_lanes
                    .iter()
                    .any(|lane| lane.source == donor.source),
                "{name} L{}: aliased column split across parts",
                selected.window.layer
            );
            // Slot-identity partition: the original plan with the same lane rebound in part 1.
            let ub = units(before).unwrap();
            let kb = unit_keys(before, &ub).unwrap();
            let part_units = units(&plan.parts[1]).unwrap();
            let part_keys = unit_keys(&plan.parts[1], &part_units).unwrap();
            let moved = part_keys
                .iter()
                .position(|k| *k == kb[target_index])
                .unwrap();
            let moved_word =
                4 * part_units[moved].first + (target.word as usize - 4 * ub[target_index].first);
            let mut naive = clone_plan(&plan);
            for part in &mut naive.parts {
                part.source_slots = aliased.source_slots.clone();
            }
            rebind(
                &mut naive.parts[1],
                WindowSourceLane {
                    word: moved_word as u32,
                    source: target.source,
                },
                alias,
            );
            assert!(
                !check(&aliased, &naive, 8).is_empty(),
                "{name} L{}: oracle accepted an alias split",
                selected.window.layer
            );
            exercised += 1;
        }
    }
    assert!(
        exercised > 0,
        "no corpus program allowed an alias construction"
    );
}

/// Two units bound to the same procedural slot share no bytes and are not linked: the plan
/// still has min(K, components-without-procedural) parts, and the oracle counts a procedural
/// slot as zero bytes.
#[test]
fn cpu_partition_procedural_sources_do_not_link() {
    let mut exercised = 0;
    for name in crate::backward::corpus_tests::CORPUS {
        let dag = load_dag(name);
        for selected in selected_programs(&dag) {
            let before = &selected.window;
            let plan = partition_r0_window(before, 8).unwrap();
            if plan.parts.len() < 2 {
                continue;
            }
            let physical = physical_slots(before).unwrap();
            let Some(procedural) = physical.iter().position(|p| p.is_none()) else {
                continue;
            };
            let procedural = procedural as u16;
            let window =
                &before.windows[usize::from(before.source_slots[usize::from(procedural)] >> 7)];
            let procedural_width = match window.backing_field() {
                FieldKind::Base => 4,
                FieldKind::Ext => 16,
            };
            let width = |slot: u16| physical[usize::from(slot)].as_ref().map(|p| p.2);
            let accept = |lane: &WindowSourceLane| width(lane.source) == Some(procedural_width);
            let (Some((_, a)), Some((_, b))) = (
                lane_in_part(before, &plan, 0, accept),
                lane_in_part(before, &plan, 1, accept),
            ) else {
                continue;
            };
            let mut rebound = before.clone();
            rebind(&mut rebound, a, procedural);
            rebind(&mut rebound, b, procedural);
            if validate_window_source_lanes(&rebound).is_err() {
                continue;
            }
            let us = units(&rebound).unwrap();
            let sources = unit_sources(&rebound, &us).unwrap();
            let by_word = lanes_by_word(&rebound).unwrap();
            let rebound_physical = physical_slots(&rebound).unwrap();
            let linked: Vec<BTreeSet<Physical>> = us
                .iter()
                .map(|u| {
                    (4 * u.first..4 * (u.first + u.records))
                        .filter_map(|word| by_word.get(&(word as u32)))
                        .map(|&slot| {
                            rebound_physical[usize::from(slot)]
                                .clone()
                                .unwrap_or_else(|| ("procedural".into(), usize::MAX, 0))
                        })
                        .collect()
                })
                .collect();
            let real = components(&sources);
            if components(&linked) >= real {
                continue;
            }
            // Requesting one part per real component isolates every component in its own
            // bin, so a planner that linked on the procedural slot would lose a part and
            // merge the two rebound units.
            let rebound_plan = partition_r0_window(&rebound, real).unwrap();
            let errors = check(&rebound, &rebound_plan, real);
            assert!(
                errors.is_empty(),
                "{name} L{}: {errors:?}",
                selected.window.layer
            );
            assert_eq!(
                rebound_plan.parts.len(),
                real,
                "{name} L{}: procedural sharing changed the part count",
                selected.window.layer
            );
            let holders: BTreeSet<usize> = rebound_plan
                .parts
                .iter()
                .enumerate()
                .filter(|(_, part)| {
                    part.source_lanes
                        .iter()
                        .any(|lane| lane.source == procedural)
                })
                .map(|(index, _)| index)
                .collect();
            assert!(
                holders.len() >= 2,
                "{name} L{}: procedural slot pulled its units into one part",
                selected.window.layer
            );
            exercised += 1;
        }
    }
    assert!(
        exercised > 0,
        "no corpus program allowed a procedural construction"
    );
}
