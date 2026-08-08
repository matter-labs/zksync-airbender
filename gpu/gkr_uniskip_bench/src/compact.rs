//! The v3 R1 COMPACTION SCHEDULE: the static (phase, round, lane) -> (element,
//! twiddle) map that lets the shuffle-NTT's real multiplies be packed across lanes.
//!
//! R0 binds lane = tap, so a stage's twiddle is a per-lane constant and the ~62 unity
//! multiplies of the 112 a group issues are *lane-divergent* — the warp instruction has
//! to serve unity and non-unity lanes at once, so a unity slot cannot be skipped. Stage
//! the group vectors in shared memory and that binding dissolves: an element is a shared
//! address, any lane can own any element, and the schedule below packs only the 50 real
//! multiplies per group into `ceil(G * m_s / 32)` rounds per stage.
//!
//! The schedule is host-built and uploaded, so this module is the single source of truth
//! and `cpu_compact_schedule_*` checks it against [`crate::domain::ntt_twiddles`] rather
//! than against a device-side twin.

use field::Field;

use crate::abi::*;
use crate::domain::{ntt_twiddles, F};

/// What a phase does to the elements it touches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhaseKind {
    /// iDIF: butterfly, then the twiddle on the high element.
    PairDif,
    /// A distance-1 butterfly with no twiddle at all (both are unity on every lane).
    PairPlain,
    /// The folded normalize+twist: diagonal, non-unity on every element.
    Twist,
    /// DIT: the twiddle on the high element, then butterfly.
    PairDit,
}

/// One phase of the factorized chain.
#[derive(Clone, Copy, Debug)]
pub struct Phase {
    pub kind: PhaseKind,
    /// Butterfly distance; `0` for [`PhaseKind::Twist`].
    pub distance: usize,
    /// Index into [`crate::domain::ntt_twiddles`], or `None` for a plain butterfly.
    pub table: Option<usize>,
}

/// The chain in execution order — the same one `uniskip_lsb_coset` walks, split into
/// phases at the points where the element-to-element dependency changes.
pub const PHASES: [Phase; 9] = [
    Phase {
        kind: PhaseKind::PairDif,
        distance: 8,
        table: Some(0),
    },
    Phase {
        kind: PhaseKind::PairDif,
        distance: 4,
        table: Some(1),
    },
    Phase {
        kind: PhaseKind::PairDif,
        distance: 2,
        table: Some(2),
    },
    Phase {
        kind: PhaseKind::PairPlain,
        distance: 1,
        table: None,
    },
    Phase {
        kind: PhaseKind::Twist,
        distance: 0,
        table: Some(3),
    },
    Phase {
        kind: PhaseKind::PairPlain,
        distance: 1,
        table: None,
    },
    Phase {
        kind: PhaseKind::PairDit,
        distance: 2,
        table: Some(4),
    },
    Phase {
        kind: PhaseKind::PairDit,
        distance: 4,
        table: Some(5),
    },
    Phase {
        kind: PhaseKind::PairDit,
        distance: 8,
        table: Some(6),
    },
];

impl Phase {
    /// Elements one lane handles per round: a pair phase moves two, the twist one.
    pub fn elements_per_lane(&self) -> usize {
        match self.kind {
            PhaseKind::Twist => 1,
            _ => 2,
        }
    }

    /// Rounds this phase needs for `groups` groups: every element is touched exactly
    /// once, 32 lanes at a time.
    pub fn rounds(&self, groups: usize) -> usize {
        groups * UNISKIP_TAPS / (self.elements_per_lane() * 32)
    }

    /// The low element of each of this phase's pairs, in increasing order; the whole
    /// element range for the twist.
    fn slots(&self) -> Vec<usize> {
        match self.kind {
            PhaseKind::Twist => (0..UNISKIP_TAPS).collect(),
            _ => (0..UNISKIP_TAPS)
                .filter(|i| i & self.distance == 0)
                .collect(),
        }
    }

    /// The element this phase's twiddle multiplies, given the slot: the HIGH element of
    /// a pair, the element itself for the twist.
    fn multiplied(&self, slot: usize) -> usize {
        match self.kind {
            PhaseKind::Twist => slot,
            _ => slot | self.distance,
        }
    }

    /// The twiddle at `slot`, or `None` when this phase multiplies nothing there — which
    /// is what the compaction packs against.
    fn twiddle(&self, tables: &[[F; UNISKIP_TAPS]; UNISKIP_NTT_TABLES], slot: usize) -> Option<F> {
        let table = self.table?;
        let value = tables[table][self.multiplied(slot)];
        (value != F::ONE).then_some(value)
    }

    /// Slots split into (multiplying, not multiplying), each in increasing order. The
    /// multiplying ones go first in the schedule, which is the whole mechanism: they
    /// then occupy a dense prefix of the phase's rounds.
    fn partition(
        &self,
        tables: &[[F; UNISKIP_TAPS]; UNISKIP_NTT_TABLES],
    ) -> (Vec<usize>, Vec<usize>) {
        self.slots()
            .into_iter()
            .partition(|&slot| self.twiddle(tables, slot).is_some())
    }

    /// Rounds of this phase that carry a multiply instruction — `ceil(G * m / 32)`. The
    /// device emits multiply code only for these, which is why unity work costs nothing
    /// rather than being predicated off.
    pub fn mul_rounds(&self, groups: usize) -> usize {
        let m = self.partition(&ntt_twiddles()).0.len();
        (groups * m).div_ceil(32)
    }
}

/// Total rounds of the whole chain at `groups` groups per warp.
pub fn total_rounds(groups: usize) -> usize {
    PHASES.iter().map(|p| p.rounds(groups)).sum()
}

/// Multiply instructions the whole chain issues per warp, and the lane-multiplies that
/// works out to per group — the number the SASS proof is checked against (R0 issues
/// `7 * 16 = 112` per group).
pub fn mul_instructions(groups: usize) -> usize {
    PHASES.iter().map(|p| p.mul_rounds(groups)).sum()
}

pub fn lane_muls_per_group(groups: usize) -> usize {
    mul_instructions(groups) * 32 / groups
}

/// BANK PERMUTATION. A round touches `32 / groups` slots of every group at once, so the
/// staging address `perm(tap) * groups + group` is conflict-free exactly when those slots
/// have distinct `perm` values modulo `32 / groups`.
///
/// Which tap permutation the staging layout uses. `Identity` is kept reachable so the
/// bank-conflict A/B is a re-runnable arm rather than a one-off claim; `Linear` is what
/// ships.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum BankPerm {
    /// The v3 R1 first build: element `(g, t)` at `t * groups + g`. Conflicts, badly.
    Identity,
    /// The GF(2)-linear map with column images `[1, 2, 5, 14]`.
    #[default]
    Linear,
}

impl BankPerm {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Identity => "identity",
            Self::Linear => "linear",
        }
    }
}

/// The slots of a distance-`d` phase are the taps with bit `log2(d)` clear — one of the
/// four coordinate hyperplanes of the 4-bit tap index, which is why the identity map
/// collides: `{0,1,2,3,8,9,10,11}` is pairwise congruent mod 8. Measured on this layout,
/// [`BankPerm::Identity`] runs **60 %** over the ideal shared-wavefront count against
/// `Linear`'s 19 %. (The 79 % figure in earlier notes belongs to a deleted group-major
/// layout, not to this one.)
///
/// [`BankPerm::Linear`] is the GF(2)-linear map with column images `[1, 2, 5, 14]`,
/// i.e. `(t0, t1, t2, t3) -> (t0^t2, t1^t3, t2^t3, t3)`. It is **a** linear permutation
/// found by enumeration, not a unique or canonical one: of the 20 160 invertible
/// GF(2) 4x4 maps, 1 344 keep the low 3 bits bijective on all four hyperplanes and
/// **768** are additionally conflict-free under [`ordered_slots`]' greedy at both group
/// counts. The hyperplane property is necessary but NOT the operative acceptance test —
/// `[1, 2, 4, 15]` has it and still conflicts at `groups = 8`. The operative test is the
/// measured one, `cpu_compact_schedule_is_bank_conflict_free`.
pub const fn bank_perm(perm: BankPerm, tap: usize) -> usize {
    match perm {
        BankPerm::Identity => tap,
        BankPerm::Linear => {
            (tap & 1) ^ ((tap >> 2) & 1)
                | ((((tap >> 1) & 1) ^ ((tap >> 3) & 1)) << 1)
                | ((((tap >> 2) & 1) ^ ((tap >> 3) & 1)) << 2)
                | (((tap >> 3) & 1) << 3)
        }
    }
}

/// The permutation as the device reads it: a 16-entry `__constant__` table, so the
/// formula lives in exactly one place.
pub fn bank_perm_words(perm: BankPerm) -> [u32; UNISKIP_TAPS] {
    core::array::from_fn(|t| bank_perm(perm, t) as u32)
}

/// Staging offset of `(group, tap)`. Group in the LOW bits, so consecutive lanes of a
/// round hit consecutive banks.
pub const fn staging_offset(perm: BankPerm, groups: usize, group: usize, tap: usize) -> usize {
    bank_perm(perm, tap) * groups + group
}

/// Order a phase's slots so that (a) the multiplying ones form a dense prefix — the
/// compaction — and (b) each round's window of `32 / groups` consecutive entries spreads
/// over distinct banks. Greedy within each partition, which is enough: at `groups = 4`
/// the window is a whole hyperplane and [`bank_perm`] already guarantees it.
fn ordered_slots(
    perm: BankPerm,
    groups: usize,
    multiplying: Vec<usize>,
    plain: Vec<usize>,
) -> Vec<usize> {
    let window = 32 / groups;
    let mut out: Vec<usize> = Vec::with_capacity(multiplying.len() + plain.len());
    let mut used: Vec<usize> = Vec::with_capacity(window);
    for mut partition in [multiplying, plain] {
        while !partition.is_empty() {
            if out.len() % window == 0 {
                used.clear();
            }
            let pick = partition
                .iter()
                .position(|&slot| !used.contains(&(bank_perm(perm, slot) % window)))
                .unwrap_or(0);
            let slot = partition.remove(pick);
            used.push(bank_perm(perm, slot) % window);
            out.push(slot);
        }
    }
    out
}

/// Build the flat `rounds * 32` schedule: entry `[round * 32 + lane]` is what that lane
/// does in that round.
///
/// Within a phase the flat work index `j` runs over `groups * slots` items, multiplying
/// slots first. It decomposes as `group = j % groups`, `k = j / groups` — `groups` is a
/// power of two, so the device does this with a mask and a shift and never divides by a
/// runtime value.
pub fn schedule(perm: BankPerm, groups: usize) -> Vec<UniskipCompactSlot> {
    assert!(
        groups.is_power_of_two() && (2..=UNISKIP_COMPACT_MAX_GROUPS).contains(&groups),
        "groups {groups} must be a power of two in 2..={UNISKIP_COMPACT_MAX_GROUPS}"
    );
    let tables = ntt_twiddles();
    let mut out = Vec::with_capacity(total_rounds(groups) * 32);
    for phase in &PHASES {
        let (multiplying, plain) = phase.partition(&tables);
        let carried = multiplying.len();
        let order = ordered_slots(perm, groups, multiplying, plain);
        let items = groups * order.len();
        assert_eq!(items, phase.rounds(groups) * 32);
        for j in 0..items {
            let (group, k) = (j % groups, j / groups);
            let slot = order[k];
            let tw = if k < carried {
                phase.twiddle(&tables, slot).unwrap().raw_u32_value()
            } else {
                0
            };
            out.push(UniskipCompactSlot {
                lo: staging_offset(perm, groups, group, slot) as u16,
                hi: staging_offset(perm, groups, group, phase.multiplied(slot)) as u16,
                tw,
            });
        }
    }
    out
}

/// The schedule padded to the device symbol's fixed size, so one upload serves either
/// group count and a stale tail can never be read as live work.
pub fn schedule_words(perm: BankPerm, groups: usize) -> Vec<UniskipCompactSlot> {
    let mut out = schedule(perm, groups);
    out.resize(
        UNISKIP_COMPACT_MAX_ROUNDS * 32,
        UniskipCompactSlot::default(),
    );
    out
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use std::collections::HashMap;

    /// G0-equivalent for R1: the schedule must touch every element of every group
    /// exactly once per phase, carry a twiddle on exactly the non-unity ones, and carry
    /// the value `domain::ntt_twiddles` says — checked against the census, not against a
    /// device-side twin.
    #[test]
    fn cpu_compact_schedule_covers_every_element_once() {
        let tables = ntt_twiddles();
        for groups in [4usize, 8] {
            let perm = BankPerm::Linear;
            let sched = schedule(perm, groups);
            assert_eq!(sched.len(), total_rounds(groups) * 32);

            let mut at = 0usize;
            for (p, phase) in PHASES.iter().enumerate() {
                let items = phase.rounds(groups) * 32;
                let slice = &sched[at..at + items];
                at += items;

                // Every (group, slot) of this phase exactly once.
                let mut seen: HashMap<(usize, usize), u32> = HashMap::new();
                let unperm: Vec<usize> = (0..UNISKIP_TAPS)
                    .map(|t| {
                        (0..UNISKIP_TAPS)
                            .position(|x| bank_perm(perm, x) == t)
                            .unwrap()
                    })
                    .collect();
                for entry in slice {
                    let group = entry.lo as usize % groups;
                    let slot = unperm[entry.lo as usize / groups];
                    assert!(group < groups, "phase {p}: group {group} out of range");
                    assert_eq!(
                        entry.hi as usize,
                        staging_offset(perm, groups, group, phase.multiplied(slot)),
                        "phase {p}: hi does not pair with lo"
                    );
                    assert!(
                        seen.insert((group, slot), entry.tw).is_none(),
                        "phase {p}: ({group}, {slot}) scheduled twice"
                    );
                }
                assert_eq!(seen.len(), groups * phase.slots().len());

                // The twiddle is exactly the non-unity entry of the census table, and a
                // unity element carries NO multiply at all.
                for (&(group, slot), &tw) in &seen {
                    let _ = group;
                    match phase.twiddle(&tables, slot) {
                        Some(want) => assert_eq!(
                            tw,
                            want.raw_u32_value(),
                            "phase {p} slot {slot}: wrong twiddle"
                        ),
                        None => assert_eq!(tw, 0, "phase {p} slot {slot}: unity was scheduled"),
                    }
                }

                // The multiplying entries occupy a DENSE PREFIX — that is the whole
                // mechanism, and it is what makes `mul_rounds` an upper bound the device
                // can lower into compile-time-guarded code.
                let carried = slice.iter().filter(|e| e.tw != 0).count();
                assert_eq!(carried, groups * phase.partition(&tables).0.len());
                assert!(
                    slice[..carried].iter().all(|e| e.tw != 0),
                    "phase {p}: multiplying entries are not a prefix"
                );
                assert!(slice[carried..].iter().all(|e| e.tw == 0));
                assert_eq!(phase.mul_rounds(groups), carried.div_ceil(32));
            }
            assert_eq!(at, sched.len());
        }
    }

    /// The counts the probe is measured against, and the R0 figure they replace.
    #[test]
    fn cpu_compact_mul_census() {
        let tables = ntt_twiddles();
        let per_phase: Vec<usize> = PHASES
            .iter()
            .map(|p| p.partition(&tables).0.len())
            .collect();
        assert_eq!(per_phase, vec![7, 6, 4, 0, 16, 0, 4, 6, 7]);
        assert_eq!(per_phase.iter().sum::<usize>(), 50);

        // LOAD-BEARING INVARIANT. `Phase::twiddle` only ever inspects the MULTIPLIED
        // element, so a non-unity entry on a pair's LOW element would be silently
        // dropped — the schedule would omit a multiply R0 still issues, and every other
        // test here would stay green. The butterfly stages put unity on the low half by
        // construction; pin it rather than trust it.
        for (p, phase) in PHASES.iter().enumerate() {
            let Some(table) = phase.table else { continue };
            if phase.kind == PhaseKind::Twist {
                assert!(
                    (0..UNISKIP_TAPS).all(|t| tables[table][t] != F::ONE),
                    "phase {p}: the twist must be non-unity everywhere"
                );
                continue;
            }
            for slot in phase.slots() {
                assert_eq!(
                    tables[table][slot],
                    F::ONE,
                    "phase {p}: low element {slot} carries a twiddle the schedule drops"
                );
            }
        }

        // R0 issues 7 unconditional multiplies on each of 16 lanes = 112 per group.
        assert_eq!(
            PHASES.iter().filter(|p| p.table.is_some()).count() * UNISKIP_TAPS,
            112
        );
        assert_eq!(
            PHASES.iter().map(|p| p.mul_rounds(8)).collect::<Vec<_>>(),
            vec![2, 2, 1, 0, 4, 0, 1, 2, 2]
        );
        assert_eq!(mul_instructions(8), 14);
        assert_eq!(lane_muls_per_group(8), 56);
        assert_eq!(mul_instructions(4), 8);
        assert_eq!(lane_muls_per_group(4), 64);
        assert_eq!(total_rounds(8), 20);
        assert_eq!(total_rounds(4), 10);
        assert!(total_rounds(8) <= UNISKIP_COMPACT_MAX_ROUNDS);
    }

    /// F1: the schedule must RUN, not merely look well-formed. Executes the generated
    /// schedule's phase semantics over a host staging buffer — the same order, the same
    /// multiply sites — and demands bit-exact agreement with
    /// [`crate::domain::coset_from_taps`]. Swapping the DIF multiply site (high before
    /// the butterfly instead of after) leaves every structural test green and fails this
    /// one.
    #[test]
    fn cpu_compact_schedule_executes_the_chain() {
        use crate::domain::{coset_from_taps, mul};

        let perm = BankPerm::Linear;
        for groups in [4usize, 8] {
            let sched = schedule(perm, groups);
            for case in 0..24u32 {
                // Random and adversarial group-sets, and every E4 limb position by
                // construction: the transform is bf-linear per limb, so a limb IS a
                // group-set here.
                let taps: Vec<[F; UNISKIP_TAPS]> = (0..groups)
                    .map(|g| {
                        core::array::from_fn(|t| match case {
                            0 => F::ZERO,
                            1 => F::new(F::ORDER - 1),
                            2 => {
                                if (g + t) % 2 == 0 {
                                    F::new(F::ORDER - 1)
                                } else {
                                    F::ONE
                                }
                            }
                            _ => F::new(
                                (case as u64 * 0x9e37_79b9
                                    + (g * UNISKIP_TAPS + t) as u64 * 0x85eb_ca6b
                                        % u64::from(F::ORDER))
                                    as u32
                                    % F::ORDER,
                            ),
                        })
                    })
                    .collect();

                // Stage exactly as the device does, run the schedule, read back.
                let mut buf = vec![F::ZERO; groups * UNISKIP_TAPS];
                for (g, group) in taps.iter().enumerate() {
                    for (t, v) in group.iter().enumerate() {
                        buf[staging_offset(perm, groups, g, t)] = *v;
                    }
                }
                let mut at = 0usize;
                for phase in &PHASES {
                    let items = phase.rounds(groups) * 32;
                    for entry in &sched[at..at + items] {
                        let (lo, hi) = (entry.lo as usize, entry.hi as usize);
                        let tw = (entry.tw != 0).then(|| F::from_raw_u32(entry.tw));
                        if phase.kind == PhaseKind::Twist {
                            buf[lo] = mul(buf[lo], tw.expect("the twist multiplies every element"));
                            continue;
                        }
                        let (a, mut b) = (buf[lo], buf[hi]);
                        if phase.kind == PhaseKind::PairDit {
                            if let Some(tw) = tw {
                                b = mul(b, tw);
                            }
                        }
                        let mut sum = a;
                        sum.add_assign(&b);
                        let mut diff = a;
                        diff.sub_assign(&b);
                        if phase.kind == PhaseKind::PairDif {
                            if let Some(tw) = tw {
                                diff = mul(diff, tw);
                            }
                        }
                        buf[lo] = sum;
                        buf[hi] = diff;
                    }
                    at += items;
                }
                for (g, group) in taps.iter().enumerate() {
                    let want = coset_from_taps(group);
                    let got: [F; UNISKIP_TAPS] =
                        core::array::from_fn(|t| buf[staging_offset(perm, groups, g, t)]);
                    assert_eq!(got, want, "groups {groups} case {case} group {g}");
                }
            }
        }
    }

    /// The shared-memory access of every round must be conflict-free — measured on the
    /// real schedule by histogramming banks, not argued from the stride. The first build
    /// of this mode passed a stride argument and still ran at 1.79x the ideal wavefront
    /// count; this test is what that failure bought.
    #[test]
    fn cpu_compact_schedule_is_bank_conflict_free() {
        for groups in [4usize, 8] {
            let sched = schedule(BankPerm::Linear, groups);
            for (r, round) in sched.chunks(32).enumerate() {
                for (which, addrs) in [
                    ("lo", round.iter().map(|e| e.lo).collect::<Vec<_>>()),
                    ("hi", round.iter().map(|e| e.hi).collect::<Vec<_>>()),
                ] {
                    let mut banks = [0usize; 32];
                    for a in &addrs {
                        banks[*a as usize % 32] += 1;
                    }
                    let worst = banks.iter().copied().max().unwrap();
                    // A twist round names each element once, so `hi == lo` there and the
                    // two histograms coincide; a pair round names 32 distinct elements.
                    assert_eq!(
                        worst, 1,
                        "groups {groups} round {r} {which}: {worst}-way bank conflict"
                    );
                }
            }
        }
    }

    /// `bank_perm` is a bijection whose low three bits stay a bijection on each of the
    /// four tap hyperplanes a phase's slots form — the property the round's
    /// conflict-freedom rests on.
    #[test]
    fn cpu_compact_bank_perm_is_hyperplane_bijective() {
        let image: std::collections::HashSet<usize> = (0..UNISKIP_TAPS)
            .map(|t| bank_perm(BankPerm::Linear, t))
            .collect();
        assert_eq!(image.len(), UNISKIP_TAPS);
        for bit in 0..4 {
            let residues: std::collections::HashSet<usize> = (0..UNISKIP_TAPS)
                .filter(|t| t >> bit & 1 == 0)
                .map(|t| bank_perm(BankPerm::Linear, t) % 8)
                .collect();
            assert_eq!(residues.len(), 8, "bit {bit} hyperplane collides mod 8");
        }
        // The map is GF(2)-linear with column images [1, 2, 5, 14].
        for t in 0..UNISKIP_TAPS {
            let linear = (0..4).fold(0usize, |acc, b| {
                acc ^ if t >> b & 1 == 1 { [1, 2, 5, 14][b] } else { 0 }
            });
            assert_eq!(bank_perm(BankPerm::Linear, t), linear, "tap {t}");
        }
    }
}
