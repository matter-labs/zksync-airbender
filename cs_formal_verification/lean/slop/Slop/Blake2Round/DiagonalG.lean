module
public import Slop.Blake2Round.ColumnG

@[expose] public section

set_option warningAsError true

/-!
The four diagonal G calls. Call `k` mixes lanes `k, 4 + (k+1)%4, 8 + (k+2)%4,
12 + (k+3)%4` after the column step, with scheduled message words `8 + 2k, 9 + 2k`.
Its inputs are the output expressions of column calls `k`, `k+1`, `k+2`, `k+3`
(mod 4); its outputs are the write columns of the extended state words of those
lanes. Its thirty allocated columns start at `416 + 30k` and its queries are
fixed-table queries `64 + 16k ..`. Where the circuit uses a write column, the
carry and the high chunk are the expressions `(sum - write) / 2^16` and
`(write - low) / 2^j`.
-/

namespace Airbender.Blake2Round.Proofs

set_option maxHeartbeats 4000000

/-- First limb of extended state word `i` as written back to memory. -/
def writeLane (i : Nat) : Nat := 39 + 4 * i

def diagonalTrace {p : Nat} (k : Nat) (w : Nat → ZMod p) : GTrace p :=
  let ca := columnTrace k w
  let cb := columnTrace ((k + 1) % 4) w
  let cc := columnTrace ((k + 2) % 4) w
  let cd := columnTrace ((k + 3) % 4) w
  let v : Nat → ZMod p := fun i => w (416 + 30 * k + i)
  let aLo := ca.a2Lo
  let aHi := ca.a2Hi
  let bLo := cb.b2Lo
  let bHi := cb.b2Hi
  let cLo := cc.c2Lo
  let cHi := cc.c2Hi
  let yLo := w (242 + 4 * k)
  let yHi := w (243 + 4 * k)
  let a1Lo := aLo + bLo + w (240 + 4 * k) - 65536 * v 1
  let a1Hi := aHi + bHi + w (241 + 4 * k) + v 1 - 65536 * v 3
  let c1Lo := cLo + (v 6 + 256 * v 7) - 65536 * v 10
  let c1Hi := cHi + (v 4 + 256 * v 5) + v 10 - 65536 * v 13
  let a2Lo := w (writeLane k)
  let a2Hi := w (writeLane k + 1)
  let b2Lo := w (writeLane (4 + (k + 1) % 4))
  let b2Hi := w (writeLane (4 + (k + 1) % 4) + 1)
  let c2Lo := w (writeLane (8 + (k + 2) % 4))
  let c2Hi := w (writeLane (8 + (k + 2) % 4) + 1)
  let d2Lo := w (writeLane (12 + (k + 3) % 4))
  let d2Hi := w (writeLane (12 + (k + 3) % 4) + 1)
  let kb0 := (-30720 : ZMod p) * (a1Lo + (v 20 + 128 * v 19) + yLo - a2Lo)
  let s3 := (-7864320 : ZMod p) * (d2Lo - v 24)
  let s2 := (-7864320 : ZMod p) * (d2Hi - v 25)
  let kd0 := (-30720 : ZMod p) * (c1Lo + (v 24 + 256 * s3) - c2Lo)
  { aLo := aLo, aHi := aHi, bLo := bLo, bHi := bHi, cLo := cLo, cHi := cHi,
    dLo := cd.d2Lo, dHi := cd.d2Hi, xLo := w (240 + 4 * k), xHi := w (241 + 4 * k),
    yLo := yLo, yHi := yHi,
    d0 := cd.s0, d1 := cd.s3, d2 := cd.s1, d3 := cd.s2,
    a1b0 := v 0, a1b1 := (-7864320 : ZMod p) * (a1Lo - v 0),
    a1b2 := v 2, a1b3 := (-7864320 : ZMod p) * (a1Hi - v 2),
    ka0 := v 1, ka1 := v 3, r0 := v 4, r1 := v 5, r2 := v 6, r3 := v 7,
    c3lo := v 8, c9lo := v 9, c4lo := (-491520 : ZMod p) * (c1Lo - (v 8 + 8 * v 9)),
    c3hi := v 11, c9hi := v 12, c4hi := (-491520 : ZMod p) * (c1Hi - (v 11 + 8 * v 12)),
    kc0 := v 10, kc1 := v 13,
    b3lo := v 14, b9lo := v 15, b4lo := (-491520 : ZMod p) * (bLo - (v 14 + 8 * v 15)),
    b3hi := v 16, b9hi := v 17, b4hi := (-491520 : ZMod p) * (bHi - (v 16 + 8 * v 17)),
    x9lo := v 18, x9hi := v 19, x7lo := v 20, x7hi := v 21,
    a2b0 := v 22, a2b1 := (-7864320 : ZMod p) * (a2Lo - v 22),
    a2b2 := v 23, a2b3 := (-7864320 : ZMod p) * (a2Hi - v 23),
    kb0 := kb0, kb1 := (-30720 : ZMod p) * (a1Hi + (v 21 + 128 * v 18) + yHi + kb0 - a2Hi),
    s0 := v 24, s1 := v 25, s2 := s2, s3 := s3,
    c2l0 := v 26, c2h0 := (-15728640 : ZMod p) * (c2Lo - v 26),
    c2l1 := v 27, c2h1 := (-15728640 : ZMod p) * (c2Hi - v 27),
    kd0 := kd0, kd1 := (-30720 : ZMod p) * (c1Hi + (v 25 + 256 * s2) + kd0 - c2Hi),
    t0 := v 28, t1 := v 29, t2 := (-3932160 : ZMod p) * (b2Hi - v 29),
    t3 := (-3932160 : ZMod p) * (b2Lo - v 28),
    a2Lo := a2Lo, a2Hi := a2Hi, b2Lo := b2Lo, b2Hi := b2Hi,
    c2Lo := c2Lo, c2Hi := c2Hi, d2Lo := d2Lo, d2Hi := d2Hi }

/-- An evaluated query column is the named field of a diagonal trace. -/
macro "diagonal_eq" : tactic => `(tactic| (
  simp only [diagonalTrace, columnTrace, columnDLane, writeLane, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceMod]
  try mod_ring))

/-- The limb equations of a diagonal call hold by construction, with BabyBear inverses. -/
theorem diagonal_limbs {p : Nat} [Fact p.Prime] (compatible : 64 * (-31457280 : ZMod p) = 1)
    (k : Nat) (w : Nat → ZMod p) : (diagonalTrace k w).Limbs := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  constructor <;> simp only [diagonalTrace, columnTrace] <;> mod_ring

end Airbender.Blake2Round.Proofs
