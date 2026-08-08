//! The v3 R2 PAIR-RESIDENT chain: the host model of a divergent-free radix-2 butterfly.
//!
//! R0 binds lane = tap, so a butterfly's two halves live in different lanes and the stage
//! reads as `val = (lane & d) ? partner - val : val + partner` followed by an
//! unconditional multiply — a multiply that is unity on half the lanes and cannot be
//! skipped because the halves are lane-divergent. R1 removed those unity multiplies by
//! staging in shared memory and paid more for the medium than the multiplies were worth.
//!
//! Pack the PAIR into one lane and the problem dissolves in the source text: the stage is
//! `lo = u + v; hi = (u - v) * w`, and the low output's unity multiply **never exists**.
//! No shared memory, no schedule table — the register medium, with the multiply cut.
//!
//! A group's 16 taps live on [`PAIR_LANES`] lanes, two per lane. The pairing a stage needs
//! changes with its butterfly distance, so between stages each lane keeps one output and
//! trades the other: one `shfl_xor` per re-pair, six for the whole chain.

use field::Field;

use crate::abi::UNISKIP_TAPS;
use crate::domain::{mul, ntt_twiddles, F};

/// Lanes one group occupies: 16 taps at 2 per lane.
pub const PAIR_LANES: usize = UNISKIP_TAPS / 2;
/// Groups a warp holds, and therefore rows per warp.
pub const PAIR_GROUPS_PER_WARP: usize = 32 / PAIR_LANES;

/// Element index of `(lane, slot)` while the chain is pairing on bit `b`: the lane index
/// supplies every tap bit except `b`, and the slot supplies bit `b`. A bijection onto
/// `0..16` at every stage, which is what makes the pairing well defined.
pub const fn element_at(lane: usize, bit: usize, slot: usize) -> usize {
    ((lane >> bit) << (bit + 1)) | (slot << bit) | (lane & ((1 << bit) - 1))
}

/// What a stage does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairStage {
    /// iDIF: `lo = u + v`, `hi = (u - v) * w`.
    Dif,
    /// A distance-1 butterfly whose twiddle is unity on every element — no multiply at all.
    Plain,
    /// The folded normalize+twist: both of the lane's elements are multiplied.
    Twist,
    /// DIT: `v *= w`, then `lo = u + v`, `hi = u - v`.
    Dit,
}

/// The chain in execution order: `(stage, pairing bit, twiddle table)`.
pub const PAIR_CHAIN: [(PairStage, usize, Option<usize>); 9] = [
    (PairStage::Dif, 3, Some(0)),
    (PairStage::Dif, 2, Some(1)),
    (PairStage::Dif, 1, Some(2)),
    (PairStage::Plain, 0, None),
    (PairStage::Twist, 0, Some(3)),
    (PairStage::Plain, 0, None),
    (PairStage::Dit, 1, Some(4)),
    (PairStage::Dit, 2, Some(5)),
    (PairStage::Dit, 3, Some(6)),
];

/// The `shfl_xor` mask that re-pairs from bit `b` to bit `b_next`. In the lane index at
/// stage `b` — the tap index with bit `b` deleted — the bit that must be traded is
/// `b_next`, shifted down by one when it sat above the deleted bit.
pub const fn repair_mask(bit: usize, next: usize) -> usize {
    1 << if next < bit { next } else { next - 1 }
}

/// The chain's re-pair masks in order. Six, against R0's eight partner-fetches — and each
/// serves a whole pair rather than one element, so a group's shuffle traffic falls from
/// `8 x 16` lane-exchanges to `6 x 8`.
pub fn repair_masks() -> Vec<usize> {
    let bits: Vec<usize> = PAIR_CHAIN.iter().map(|s| s.1).collect();
    bits.windows(2)
        .filter(|w| w[0] != w[1])
        .map(|w| repair_mask(w[0], w[1]))
        .collect()
}

/// Multiplies the chain issues per group: one per lane at each of the six twiddled
/// butterfly stages, plus two per lane at the twist. R0 issues `7 x 16 = 112`.
pub fn issued_muls_per_group() -> usize {
    PAIR_CHAIN
        .iter()
        .map(|&(stage, _, table)| match (stage, table) {
            (PairStage::Twist, _) => 2 * PAIR_LANES,
            (_, Some(_)) => PAIR_LANES,
            _ => 0,
        })
        .sum()
}

/// The twiddles one lane needs, in chain order: its pair's high element at each twiddled
/// butterfly stage, then its two twist values. Eight registers, preloaded once — never a
/// lane-indexed constant read in the hot path.
pub fn lane_twiddles(lane: usize) -> Vec<F> {
    let tables = ntt_twiddles();
    let mut out = Vec::with_capacity(8);
    for &(stage, bit, table) in &PAIR_CHAIN {
        match (stage, table) {
            (PairStage::Twist, Some(t)) => {
                out.push(tables[t][element_at(lane, bit, 0)]);
                out.push(tables[t][element_at(lane, bit, 1)]);
            }
            (_, Some(t)) => out.push(tables[t][element_at(lane, bit, 1)]),
            _ => {}
        }
    }
    out
}

/// Re-pair: each lane keeps one of its two values and trades the other with the lane at
/// `lane ^ mask`. `p` — whether this lane is the high side of the trading pair — decides
/// which one stays, and both sides use the same three selects.
fn repair(pairs: &mut [(F, F); PAIR_LANES], mask: usize) {
    let sent: Vec<F> = (0..PAIR_LANES)
        .map(|l| {
            if l & mask != 0 {
                pairs[l].0
            } else {
                pairs[l].1
            }
        })
        .collect();
    for l in 0..PAIR_LANES {
        let recv = sent[l ^ mask];
        pairs[l] = if l & mask != 0 {
            (recv, pairs[l].1)
        } else {
            (pairs[l].0, recv)
        };
    }
}

/// Run the pair-resident chain over one group, in exactly the shape the kernel runs it.
/// Input and output are both in the stage-3 map: lane `l` holds taps `l` and `l + 8` on
/// the way in, and coset cells `l` and `l + 8` on the way out — the chain ends where it
/// started, so `H` and the coset share one map and the consumer needs no re-indexing.
pub fn pair_chain(taps: &[F; UNISKIP_TAPS]) -> [F; UNISKIP_TAPS] {
    let tw: Vec<Vec<F>> = (0..PAIR_LANES).map(lane_twiddles).collect();
    let mut pairs: [(F, F); PAIR_LANES] =
        core::array::from_fn(|l| (taps[element_at(l, 3, 0)], taps[element_at(l, 3, 1)]));

    let mut next_tw = 0usize;
    let mut masks = repair_masks().into_iter();
    for (i, &(stage, _, table)) in PAIR_CHAIN.iter().enumerate() {
        for (l, pair) in pairs.iter_mut().enumerate() {
            let (u, v) = *pair;
            *pair = match stage {
                PairStage::Twist => (mul(u, tw[l][next_tw]), mul(v, tw[l][next_tw + 1])),
                PairStage::Dit => {
                    let v = mul(v, tw[l][next_tw]);
                    let mut lo = u;
                    lo.add_assign(&v);
                    let mut hi = u;
                    hi.sub_assign(&v);
                    (lo, hi)
                }
                PairStage::Dif | PairStage::Plain => {
                    let mut lo = u;
                    lo.add_assign(&v);
                    let mut hi = u;
                    hi.sub_assign(&v);
                    if stage == PairStage::Dif {
                        hi = mul(hi, tw[l][next_tw]);
                    }
                    (lo, hi)
                }
            };
        }
        if table.is_some() {
            next_tw += if stage == PairStage::Twist { 2 } else { 1 };
        }
        // Re-pair whenever the next stage pairs on a different bit.
        if i + 1 < PAIR_CHAIN.len() && PAIR_CHAIN[i + 1].1 != PAIR_CHAIN[i].1 {
            repair(&mut pairs, masks.next().expect("one mask per bit change"));
        }
    }
    assert!(masks.next().is_none());

    let mut out = [F::ZERO; UNISKIP_TAPS];
    for (l, &(a, b)) in pairs.iter().enumerate() {
        out[element_at(l, 3, 0)] = a;
        out[element_at(l, 3, 1)] = b;
    }
    out
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::domain::{coset_from_taps, E4};
    use field::FieldExtension;

    fn e4_limb(x: E4, i: usize) -> F {
        [x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1][i]
    }

    /// The geometry the kernel is built on.
    #[test]
    fn cpu_pair_geometry() {
        assert_eq!(PAIR_LANES, 8);
        assert_eq!(PAIR_GROUPS_PER_WARP, 4);
        assert_eq!(repair_masks(), vec![4, 2, 1, 1, 2, 4]);
        // Every stage's map is a bijection onto the group's 16 elements.
        for bit in 0..4 {
            let seen: std::collections::HashSet<usize> = (0..PAIR_LANES)
                .flat_map(|l| (0..2).map(move |s| element_at(l, bit, s)))
                .collect();
            assert_eq!(seen.len(), UNISKIP_TAPS, "bit {bit}");
        }
        // The chain ends on the map it started on, so H and the coset share one layout.
        assert_eq!(PAIR_CHAIN[0].1, 3);
        assert_eq!(PAIR_CHAIN[PAIR_CHAIN.len() - 1].1, 3);
        // 6 twiddled butterfly stages x 8 lanes + 2 twist muls x 8 lanes.
        assert_eq!(issued_muls_per_group(), 64);
        assert_eq!(lane_twiddles(0).len(), 8);
        // R0's figure, for the ratio the record quotes.
        assert_eq!(7 * UNISKIP_TAPS, 112);
    }

    /// The pair chain must reproduce the reference coset transform exactly. Same code
    /// shape as the kernel — pair butterfly, re-pair permutation, twist — so a multiply
    /// applied at the wrong point in a butterfly fails here.
    #[test]
    fn cpu_pair_chain_matches_reference() {
        let mut cases: Vec<[F; UNISKIP_TAPS]> = vec![
            [F::ZERO; UNISKIP_TAPS],
            [F::ONE; UNISKIP_TAPS],
            [F::new(F::ORDER - 1); UNISKIP_TAPS],
            core::array::from_fn(|t| {
                if t % 2 == 0 {
                    F::new(F::ORDER - 1)
                } else {
                    F::ONE
                }
            }),
        ];
        for t in 0..UNISKIP_TAPS {
            let mut impulse = [F::ZERO; UNISKIP_TAPS];
            impulse[t] = F::new(F::ORDER - 1);
            cases.push(impulse);
        }
        for seed in 0..64u32 {
            cases.push(core::array::from_fn(|t| {
                F::new(
                    seed.wrapping_mul(0x9e37_79b9)
                        .wrapping_add((t as u32).wrapping_mul(0x85eb_ca6b))
                        % F::ORDER,
                )
            }));
        }
        for (i, taps) in cases.iter().enumerate() {
            assert_eq!(pair_chain(taps), coset_from_taps(taps), "case {i}");
        }
    }

    /// Every `E4` limb position, against a dense apply on the `E4` itself — the chain is
    /// `bf`-linear per limb, which is what lets the kernel run limb-sequentially.
    #[test]
    fn cpu_pair_chain_e4_limbs() {
        let matrix = crate::domain::lde_matrix();
        for seed in [1u32, 7, 0x1234_5678, 0xdead_beef] {
            let taps: [E4; UNISKIP_TAPS] = core::array::from_fn(|t| {
                E4::from_array_of_base(core::array::from_fn(|l| {
                    F::new(
                        seed.wrapping_add(l as u32 * 0x1000_0001)
                            .wrapping_mul(0x9e37_79b9)
                            .wrapping_add((t as u32).wrapping_mul(0x85eb_ca6b))
                            % F::ORDER,
                    )
                }))
            });
            let dense: [E4; UNISKIP_TAPS] = core::array::from_fn(|c| {
                let mut acc = E4::ZERO;
                for t in 0..UNISKIP_TAPS {
                    <E4 as FieldExtension<F>>::add_assign_product_with_base(
                        &mut acc,
                        &taps[t],
                        &matrix[c][t],
                    );
                }
                acc
            });
            for limb in 0..4 {
                let got = pair_chain(&core::array::from_fn(|t| e4_limb(taps[t], limb)));
                for c in 0..UNISKIP_TAPS {
                    assert_eq!(
                        got[c],
                        e4_limb(dense[c], limb),
                        "seed {seed} limb {limb} cell {c}"
                    );
                }
            }
        }
    }
}
