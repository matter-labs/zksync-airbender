//! The v3 R3 register window: a coset-only, top-4-BF slot schedule for `--mode lsb-pair`.
//!
//! SEMANTICS. A slot retains one BF source's produced coset pair `c[2]`; `h[2]` is still
//! loaded on reuse. A reuse therefore skips exactly the shuffle-NTT chain and its twist
//! for that operand resolution — nothing else. The window is coset-only because `h` is
//! the raw load and costs nothing to re-read, while `c` is the 8 multiplies and 6
//! re-pair shuffles the R2 chain spends per component pass.
//!
//! The schedule is expressed in the device's **resolver invocation order**
//! ([`SynthProgram::resolver_operands`]) and travels in a side descriptor keyed by record
//! position, so the control wire format is untouched and `--mode lsb-pair` without a
//! window behaves exactly as it does today.

use crate::abi::*;
use crate::synth::SynthProgram;

/// What the kernel does with one operand resolution.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WindowTag {
    /// Resolve normally — load `h`, run the chain, keep nothing.
    #[default]
    None,
    /// Resolve normally, then retain the produced `c[2]` in this slot.
    Fill(u8),
    /// Load `h`, take `c[2]` from this slot, skip the chain.
    Reuse(u8),
}

impl WindowTag {
    /// NIBBLE ENCODING. One byte per record: operand A in the LOW nibble, operand B in
    /// the high. Within a nibble, `0` is `None`, `1 + slot` is `Fill`, and
    /// `1 + SLOTS + slot` is `Reuse`. `None == 0` is deliberate — a zeroed tag array is a
    /// valid all-`None` schedule, which is exactly the control arm's wire and the `wnone`
    /// diagnostic, so neither needs a separate encoding path.
    pub fn encode(self) -> u8 {
        match self {
            Self::None => 0,
            Self::Fill(slot) => 1 + slot,
            Self::Reuse(slot) => 1 + UNISKIP_WINDOW_SLOTS as u8 + slot,
        }
    }

    pub fn decode(nibble: u8) -> Result<Self, String> {
        let slots = UNISKIP_WINDOW_SLOTS as u8;
        match nibble {
            0 => Ok(Self::None),
            n if n <= slots => Ok(Self::Fill(n - 1)),
            n if n <= 2 * slots => Ok(Self::Reuse(n - 1 - slots)),
            n => Err(format!("nibble {n} is not a window tag")),
        }
    }

    pub fn slot(self) -> Option<u8> {
        match self {
            Self::None => None,
            Self::Fill(s) | Self::Reuse(s) => Some(s),
        }
    }
}

/// Pack two operand tags into one record byte.
pub fn pack(a: WindowTag, b: WindowTag) -> u8 {
    a.encode() | (b.encode() << 4)
}

/// Unpack a record byte into `(operand A, operand B)`.
pub fn unpack(byte: u8) -> Result<(WindowTag, WindowTag), String> {
    Ok((
        WindowTag::decode(byte & 0xf)?,
        WindowTag::decode(byte >> 4)?,
    ))
}

/// A built schedule: the record-indexed tag stream plus the slot assignment it implies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowSchedule {
    /// One byte per record position; see [`WindowTag::encode`].
    pub tags: Vec<u8>,
    /// Source retained by each slot, in slot order. Shorter than
    /// [`UNISKIP_WINDOW_SLOTS`] when the program has fewer BF sources.
    pub slot_source: Vec<u16>,
    /// References the top-4 sources take, in slot order — the ranking that chose them.
    pub slot_refs: Vec<u32>,
    /// Resolutions that skip the chain: `sum(slot_refs) - slots`.
    pub reuses: u32,
    /// Component passes a warp-program walk runs without the window, width-weighted
    /// (`bf` 1, `e4` 4) — the 326 of the default census.
    pub passes_without: u32,
    /// The same with the window: `passes_without - reuses`, since every slot is `bf`.
    pub passes_with: u32,
}

impl WindowSchedule {
    /// The all-`None` schedule of the right shape: the `wnone` diagnostic, which pays the
    /// window kernel's register and branch cost and takes none of its saving.
    pub fn empty(program: &SynthProgram) -> Self {
        let passes = weighted_passes(program);
        Self {
            tags: vec![0u8; program.program.len()],
            slot_source: Vec::new(),
            slot_refs: Vec::new(),
            reuses: 0,
            passes_without: passes,
            passes_with: passes,
        }
    }

    /// The side descriptor the kernel reads. The control wire is untouched: this is a
    /// separate parameter, and a mode without a window ships [`Self::empty`]'s zeros.
    pub fn descriptor(&self) -> UniskipWindowDesc {
        let mut desc = UniskipWindowDesc {
            slot_count: self.slot_source.len() as u32,
            ..Default::default()
        };
        desc.tags[..self.tags.len()].copy_from_slice(&self.tags);
        desc.slot_source[..self.slot_source.len()].copy_from_slice(&self.slot_source);
        desc
    }
}

/// Width-weighted component passes of one warp-program walk: `bf` sources cost one pass,
/// `e4` four, counted per resolver invocation.
fn weighted_passes(program: &SynthProgram) -> u32 {
    program
        .resolver_operands()
        .iter()
        .map(|op| component_width(program.sources[op.source as usize].source_class))
        .sum()
}

/// SLOT POLICY: the top [`UNISKIP_WINDOW_SLOTS`] `bf` sources by resolver-invocation
/// reference count, ties broken by lower source id. `e4` sources are excluded — one would
/// take four slots' worth of registers for one source.
///
/// Ranked off [`SynthProgram::resolver_refs`], recomputed from the program rather than
/// read from `census.per_source_refs`, which is measured at generation and goes stale
/// under `force_self_products` or a census override.
fn select_slots(program: &SynthProgram) -> (Vec<u16>, Vec<u32>) {
    let refs = program.resolver_refs();
    let mut ranked: Vec<(u32, u16)> = program
        .sources
        .iter()
        .enumerate()
        .filter(|(_, rec)| rec.source_class == UNISKIP_SRC_BF_GLOBAL)
        .map(|(id, _)| (refs[id], id as u16))
        .filter(|&(count, _)| count > 0)
        .collect();
    ranked.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    ranked.truncate(UNISKIP_WINDOW_SLOTS);
    (
        ranked.iter().map(|&(_, id)| id).collect(),
        ranked.iter().map(|&(count, _)| count).collect(),
    )
}

/// Build the schedule for this program in its current term order and census state.
///
/// Walks the resolver order once, assigning `Fill` at a slot source's first resolution
/// and `Reuse` at every later one. A self-product's operand B gets no tag because it is
/// not a resolution — `resolve_second` short-circuits — which is why the tag stream is
/// keyed by record while the walk is keyed by invocation.
pub fn plan(program: &SynthProgram) -> WindowSchedule {
    let (slot_source, slot_refs) = select_slots(program);
    let mut tags = vec![WindowTag::None; 2 * program.program.len()];
    let mut filled = vec![false; slot_source.len()];
    let mut reuses = 0u32;

    for op in program.resolver_operands() {
        let Some(slot) = slot_source.iter().position(|&s| s == op.source) else {
            continue;
        };
        tags[2 * op.record + op.operand as usize] = if filled[slot] {
            reuses += 1;
            WindowTag::Reuse(slot as u8)
        } else {
            filled[slot] = true;
            WindowTag::Fill(slot as u8)
        };
    }

    let passes_without = weighted_passes(program);
    let schedule = WindowSchedule {
        tags: (0..program.program.len())
            .map(|r| pack(tags[2 * r], tags[2 * r + 1]))
            .collect(),
        slot_source,
        slot_refs,
        reuses,
        passes_without,
        passes_with: passes_without - reuses,
    };
    debug_assert!(
        validate(program, &schedule).is_ok(),
        "{}",
        validate(program, &schedule).unwrap_err()
    );
    schedule
}

/// INVARIANT 4, machine-checked: replay the tag stream through the slot state the kernel
/// will hold and reject anything the kernel could not execute — a reuse before its fill,
/// a reuse of a slot holding a different source, a second fill of a live slot, a tag on
/// an operand that is not a resolution, or a tag on an `e4` operand.
///
/// Runs in tests and as a `debug_assert!` on every schedule [`plan`] builds.
pub fn validate(program: &SynthProgram, schedule: &WindowSchedule) -> Result<(), String> {
    if schedule.tags.len() != program.program.len() {
        return Err(format!(
            "tag stream is {} records, program is {}",
            schedule.tags.len(),
            program.program.len()
        ));
    }
    if schedule.slot_source.len() > UNISKIP_WINDOW_SLOTS {
        return Err(format!(
            "{} slots exceed the window",
            schedule.slot_source.len()
        ));
    }

    // Only a real resolution may carry a tag; everything else must decode to `None`.
    let operands = program.resolver_operands();
    let mut live: Vec<Option<u16>> = vec![None; schedule.slot_source.len()];
    let mut tagged = vec![false; 2 * program.program.len()];

    for op in &operands {
        let byte = schedule.tags[op.record];
        let (a, b) = unpack(byte)?;
        let tag = if op.operand == 0 { a } else { b };
        tagged[2 * op.record + op.operand as usize] = true;
        let Some(slot) = tag.slot() else { continue };
        let slot = slot as usize;
        if slot >= live.len() {
            return Err(format!(
                "record {} operand {}: slot {slot} is beyond the {} assigned",
                op.record,
                op.operand,
                live.len()
            ));
        }
        if program.sources[op.source as usize].source_class != UNISKIP_SRC_BF_GLOBAL {
            return Err(format!(
                "record {} operand {}: source {} is e4 and cannot occupy a slot",
                op.record, op.operand, op.source
            ));
        }
        match tag {
            WindowTag::Fill(_) => {
                if schedule.slot_source[slot] != op.source {
                    return Err(format!(
                        "record {} operand {}: fill of slot {slot}, assigned to source {}, \
                         operand references {}",
                        op.record, op.operand, schedule.slot_source[slot], op.source
                    ));
                }
                if live[slot].is_some() {
                    return Err(format!(
                        "record {} operand {}: fill of slot {slot}, already live with source {}",
                        op.record,
                        op.operand,
                        live[slot].unwrap()
                    ));
                }
                live[slot] = Some(op.source);
            }
            WindowTag::Reuse(_) => match live[slot] {
                None => {
                    return Err(format!(
                        "record {} operand {}: reuse of slot {slot} before any fill",
                        op.record, op.operand
                    ))
                }
                Some(held) if held != op.source => {
                    return Err(format!(
                        "record {} operand {}: reuse of slot {slot} holding source {held}, \
                         operand references {}",
                        op.record, op.operand, op.source
                    ))
                }
                Some(_) => {}
            },
            WindowTag::None => unreachable!("filtered by slot()"),
        }
    }

    for record in 0..program.program.len() {
        let (a, b) = unpack(schedule.tags[record])?;
        for (operand, tag) in [(0usize, a), (1, b)] {
            if tag != WindowTag::None && !tagged[2 * record + operand] {
                return Err(format!(
                    "record {record} operand {operand} is tagged {tag:?} but is not a resolution"
                ));
            }
        }
    }

    // Every selected slot must actually be filled, or it is dead weight on the wire.
    for (slot, held) in live.iter().enumerate() {
        if held.is_none() {
            return Err(format!(
                "slot {slot} was assigned source {} but never filled",
                schedule.slot_source[slot]
            ));
        }
    }
    Ok(())
}

/// TEST-ONLY schedule corruptions. Each is something [`validate`] rejects, so they can
/// only reach the device through an unchecked upload — which is exactly what makes them
/// evidence: `Retarget` proves the kernel reads the tag's slot number rather than
/// recovering it from the operand's source id, a substitution the parity matrix alone
/// cannot see.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum WindowMutation {
    /// Point the first reuse at a different slot that is already filled with another
    /// source.
    Retarget,
}

pub fn mutate(
    program: &SynthProgram,
    schedule: &WindowSchedule,
    kind: WindowMutation,
) -> WindowSchedule {
    let mut out = schedule.clone();
    match kind {
        // The target must be LIVE at this point of the walk and hold a DIFFERENT source.
        // Picking `(slot + 1) % slots` does neither: under `--term-order locality` the
        // first reuse sits at record 1 with only slot 0 filled, so that target is an
        // unfilled slot and the device reads uninitialized slot registers — a different
        // (and undefined) experiment from the one this mutation is for. So the state
        // machine is replayed here, exactly as `validate` replays it.
        WindowMutation::Retarget => {
            let mut live: Vec<Option<u16>> = vec![None; schedule.slot_source.len()];
            for op in program.resolver_operands() {
                let (a, b) = unpack(out.tags[op.record]).expect("built schedules decode");
                let tag = if op.operand == 0 { a } else { b };
                match tag {
                    WindowTag::Fill(slot) => live[slot as usize] = Some(op.source),
                    WindowTag::Reuse(slot) => {
                        let target = live.iter().enumerate().find(|(other, held)| {
                            *other != slot as usize && held.is_some_and(|s| s != op.source)
                        });
                        let Some((target, _)) = target else { continue };
                        let swapped = WindowTag::Reuse(target as u8);
                        out.tags[op.record] = if op.operand == 0 {
                            pack(swapped, b)
                        } else {
                            pack(a, swapped)
                        };
                        return out;
                    }
                    WindowTag::None => {}
                }
            }
            panic!("no reuse with another live slot holding a different source");
        }
    }
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

    /// The audit's hot-list, reproduced by counting per resolver invocation. Fill
    /// POSITIONS differ between term orders — the orders permute the record stream — but
    /// the totals are properties of the record multiset and must not.
    #[test]
    fn cpu_window_default_census_matches_the_audit() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            let s = plan(&p);
            assert_eq!(s.slot_refs, vec![13, 13, 13, 12], "{order:?}");
            assert_eq!(s.slot_source, vec![0, 1, 2, 3], "{order:?}");
            assert_eq!(s.reuses, 47, "{order:?}");
            assert_eq!(s.passes_without, 326, "{order:?}");
            assert_eq!(s.passes_with, 279, "{order:?}");
            assert_eq!(validate(&p, &s), Ok(()), "{order:?}");
            // Exactly one fill per slot, and the rest reuses.
            let mut fills = 0;
            let mut reuses = 0;
            for &byte in &s.tags {
                let (a, b) = unpack(byte).unwrap();
                for tag in [a, b] {
                    match tag {
                        WindowTag::Fill(_) => fills += 1,
                        WindowTag::Reuse(_) => reuses += 1,
                        WindowTag::None => {}
                    }
                }
            }
            assert_eq!((fills, reuses), (4, 47), "{order:?}");
        }
        // The two orders differ in where the fills land, which is the point of checking
        // both: the schedule is per (program, term order), not per program.
        let census = plan(&program(TermOrder::Census));
        let locality = plan(&program(TermOrder::Locality));
        assert_ne!(census.tags, locality.tags);
    }

    /// Under `force_self_products` the stored census is stale, so the schedule must be
    /// built from recomputed references — and a self-product's operand B is not a
    /// resolution, so it stays untagged.
    #[test]
    fn cpu_window_self_products() {
        let mut p = program(TermOrder::Census);
        assert_eq!(p.force_self_products(12), 12);
        let s = plan(&p);
        assert_eq!(validate(&p, &s), Ok(()));

        let recomputed = p.resolver_refs();
        assert_ne!(
            recomputed, p.census.per_source_refs,
            "the stored census must go stale, or this test proves nothing"
        );
        for (slot, &source) in s.slot_source.iter().enumerate() {
            assert_eq!(s.slot_refs[slot], recomputed[source as usize]);
        }

        // Every self-product record has an untagged operand B.
        let mut checked = 0;
        for (record, term) in p.program.iter().enumerate() {
            let binary = matches!(
                term.term_class,
                UNISKIP_CLASS_PRODUCT_BF_BF | UNISKIP_CLASS_PRODUCT_E4_E4
            );
            if binary && term.source_a == term.source_b {
                let (_, b) = unpack(s.tags[record]).unwrap();
                assert_eq!(b, WindowTag::None, "record {record}");
                checked += 1;
            }
        }
        assert_eq!(checked, 12);
    }

    /// FEWER BF SOURCES THAN SLOTS must give a shorter, still-valid schedule rather than
    /// a panic or four slots with garbage in the tail.
    ///
    /// The generator cannot reach this: its smallest accepted census
    /// (`--sources 9 --semantic-terms 9 --groups 0`) still leaves 8 referenced BF
    /// sources, because it must place 4 setup-window references. So the degenerate
    /// program is hand-built here — two BF sources and one E4, which also pins that the
    /// E4 is excluded from the ranking rather than truncated out of it by luck.
    #[test]
    fn cpu_window_fewer_sources_than_slots() {
        let mut p = generate(0, Census::default()).unwrap();
        p.sources.truncate(3);
        p.sources[0].source_class = UNISKIP_SRC_BF_GLOBAL;
        p.sources[1].source_class = UNISKIP_SRC_BF_GLOBAL;
        p.sources[2].source_class = UNISKIP_SRC_E4_GLOBAL;
        p.program = vec![
            UniskipTerm {
                term_class: UNISKIP_CLASS_LINEAR_BF,
                coeff: 0,
                source_a: 0,
                source_b: UNISKIP_SOURCE_UNUSED,
            },
            UniskipTerm {
                term_class: UNISKIP_CLASS_PRODUCT_BF_BF,
                coeff: 1,
                source_a: 0,
                source_b: 1,
            },
            UniskipTerm {
                term_class: UNISKIP_CLASS_LINEAR_E4,
                coeff: 2,
                source_a: 2,
                source_b: UNISKIP_SOURCE_UNUSED,
            },
        ];

        let s = plan(&p);
        assert_eq!(
            s.slot_source,
            vec![0, 1],
            "only the two bf sources take slots"
        );
        assert_eq!(s.slot_refs, vec![2, 1]);
        assert_eq!(s.reuses, 1);
        // 2 bf refs on source 0, 1 on source 1, 1 e4 ref at width 4.
        assert_eq!(s.passes_without, 2 + 1 + 4);
        assert_eq!(s.passes_with, s.passes_without - s.reuses);
        assert_eq!(validate(&p, &s), Ok(()));

        // An e4 operand may never carry a tag, even when slots are free.
        let mut corrupt = s.clone();
        corrupt.tags[2] = pack(WindowTag::Fill(0), WindowTag::None);
        assert!(validate(&p, &corrupt).unwrap_err().contains("e4"));
    }

    /// The empty schedule is the `wnone` diagnostic and the control wire: all zeros,
    /// valid, and taking no saving.
    #[test]
    fn cpu_window_empty_is_valid() {
        let p = program(TermOrder::Census);
        let s = WindowSchedule::empty(&p);
        assert!(s.tags.iter().all(|&b| b == 0));
        assert_eq!(s.reuses, 0);
        assert_eq!(s.passes_with, s.passes_without);
        assert_eq!(validate(&p, &s), Ok(()));
        assert_eq!(s.descriptor().slot_count, 0);
    }

    /// THE VALIDATOR IS THE INVARIANT, so it is tested by corruption: each of the three
    /// failure modes invariant 4 names must be rejected.
    #[test]
    fn cpu_window_validator_rejects_corruption() {
        let p = program(TermOrder::Census);
        let good = plan(&p);
        let ops = p.resolver_operands();

        let first_reuse = |s: &WindowSchedule| {
            ops.iter()
                .find(|op| {
                    let (a, b) = unpack(s.tags[op.record]).unwrap();
                    matches!(if op.operand == 0 { a } else { b }, WindowTag::Reuse(_))
                })
                .copied()
                .expect("the default schedule has reuses")
        };
        let first_fill = ops
            .iter()
            .find(|op| {
                let (a, b) = unpack(good.tags[op.record]).unwrap();
                matches!(if op.operand == 0 { a } else { b }, WindowTag::Fill(_))
            })
            .copied()
            .unwrap();

        // (a) reuse before fill: demote the slot's fill to a reuse.
        let mut corrupt = good.clone();
        let (a, b) = unpack(corrupt.tags[first_fill.record]).unwrap();
        let demoted = match if first_fill.operand == 0 { a } else { b } {
            WindowTag::Fill(slot) => WindowTag::Reuse(slot),
            other => panic!("{other:?}"),
        };
        corrupt.tags[first_fill.record] = if first_fill.operand == 0 {
            pack(demoted, b)
        } else {
            pack(a, demoted)
        };
        let err = validate(&p, &corrupt).unwrap_err();
        assert!(err.contains("before any fill"), "{err}");

        // (b) wrong-source reuse: retarget a reuse at a slot holding another source.
        let mut corrupt = good.clone();
        let victim = first_reuse(&good);
        let (a, b) = unpack(corrupt.tags[victim.record]).unwrap();
        let slot = (if victim.operand == 0 { a } else { b }).slot().unwrap();
        let other = (slot + 1) % good.slot_source.len() as u8;
        let retargeted = WindowTag::Reuse(other);
        corrupt.tags[victim.record] = if victim.operand == 0 {
            pack(retargeted, b)
        } else {
            pack(a, retargeted)
        };
        let err = validate(&p, &corrupt).unwrap_err();
        assert!(err.contains("operand references"), "{err}");

        // (c) duplicate fill of a live slot: promote a reuse back to a fill.
        let mut corrupt = good.clone();
        let (a, b) = unpack(corrupt.tags[victim.record]).unwrap();
        let promoted = WindowTag::Fill(slot);
        corrupt.tags[victim.record] = if victim.operand == 0 {
            pack(promoted, b)
        } else {
            pack(a, promoted)
        };
        let err = validate(&p, &corrupt).unwrap_err();
        assert!(err.contains("already live"), "{err}");

        // (d) a tag on something that is not a resolution: operand B of a self-product.
        let mut selfp = program(TermOrder::Census);
        selfp.force_self_products(4);
        let mut corrupt = plan(&selfp);
        let record = selfp
            .program
            .iter()
            .position(|t| t.term_class == UNISKIP_CLASS_PRODUCT_BF_BF && t.source_a == t.source_b)
            .unwrap();
        let (a, _) = unpack(corrupt.tags[record]).unwrap();
        corrupt.tags[record] = pack(a, WindowTag::Reuse(0));
        let err = validate(&selfp, &corrupt).unwrap_err();
        assert!(err.contains("not a resolution"), "{err}");

        assert_eq!(validate(&p, &good), Ok(()));
    }

    /// Q4: `mutate` must produce the mutation it advertises — a reuse pointed at a slot
    /// that is LIVE at that walk point and holds a DIFFERENT source — under both term
    /// orders. The first version picked `(slot + 1) % slots` and under `locality` hit an
    /// unfilled slot, which the validator still rejected (so the device test still
    /// "passed") while the device was reading uninitialized registers.
    #[test]
    fn cpu_window_mutate_retargets_a_live_slot() {
        for order in [TermOrder::Census, TermOrder::Locality] {
            let p = program(order);
            let good = plan(&p);
            let bad = mutate(&p, &good, WindowMutation::Retarget);

            // Exactly one record byte moves, and only its tag's slot.
            let moved: Vec<usize> = (0..good.tags.len())
                .filter(|&r| good.tags[r] != bad.tags[r])
                .collect();
            assert_eq!(moved.len(), 1, "{order:?}");

            // Replay to the mutated operand and check the target's liveness there.
            let mut live: Vec<Option<u16>> = vec![None; good.slot_source.len()];
            let mut checked = false;
            for op in p.resolver_operands() {
                let (ga, gb) = unpack(good.tags[op.record]).unwrap();
                let (ba, bb) = unpack(bad.tags[op.record]).unwrap();
                let (gt, bt) = if op.operand == 0 { (ga, ba) } else { (gb, bb) };
                if gt != bt {
                    let (WindowTag::Reuse(from), WindowTag::Reuse(to)) = (gt, bt) else {
                        panic!("{order:?}: retarget did not stay a reuse");
                    };
                    assert_ne!(from, to, "{order:?}");
                    let held = live[to as usize];
                    assert!(held.is_some(), "{order:?}: target slot {to} is not live");
                    assert_ne!(
                        held.unwrap(),
                        op.source,
                        "{order:?}: target holds the same source"
                    );
                    checked = true;
                    break;
                }
                if let WindowTag::Fill(slot) = gt {
                    live[slot as usize] = Some(op.source);
                }
            }
            assert!(checked, "{order:?}: no mutated operand found");

            // And the rejection must be the WRONG-SOURCE one, not reuse-before-fill.
            let err = validate(&p, &bad).unwrap_err();
            assert!(err.contains("holding source"), "{order:?}: {err}");
            assert!(!err.contains("before any fill"), "{order:?}: {err}");
        }
    }

    /// The `none` arms (`wnone`, `wtnone`) ship `UniskipWindowDesc::default()` rather than
    /// an explicitly built empty schedule, so the two must be the same bytes. A
    /// `debug_assert` would not survive the release build the arms are timed with.
    #[test]
    fn cpu_window_empty_descriptor_is_all_zero() {
        let p = program(TermOrder::Census);
        assert_eq!(
            WindowSchedule::empty(&p).descriptor(),
            UniskipWindowDesc::default()
        );
    }

    /// The nibble encoding round-trips and reserves `0` for `None`.
    #[test]
    fn cpu_window_tag_encoding() {
        assert_eq!(WindowTag::None.encode(), 0);
        let mut seen = std::collections::HashSet::new();
        let mut all = vec![WindowTag::None];
        for slot in 0..UNISKIP_WINDOW_SLOTS as u8 {
            all.push(WindowTag::Fill(slot));
            all.push(WindowTag::Reuse(slot));
        }
        for tag in &all {
            let n = tag.encode();
            assert!(n < 16, "{tag:?} does not fit a nibble");
            assert!(seen.insert(n), "{tag:?} collides");
            assert_eq!(WindowTag::decode(n).unwrap(), *tag);
        }
        for a in &all {
            for b in &all {
                assert_eq!(unpack(pack(*a, *b)).unwrap(), (*a, *b));
            }
        }
        assert!(WindowTag::decode(15).is_err());
    }
}
