import Slop.Blake2Round.GSound
import Slop.Blake2Round.GRows

set_option warningAsError true

/-!
The four column G calls of the wider-table round. Call `k` mixes lanes
`k, 4 + k, 8 + k, 12 + k` of the prepared state with scheduled message words
`2k, 2k + 1`; its forty allocated columns start at `256 + 40k` and its sixteen
queries are fixed-table queries `16k .. 16k + 15` (lookups `2 + 16k ..`). Columns
that the circuit does not allocate are the linear expressions it uses instead:
remainders `(sum - chunks) / 2^j` and the sums themselves.
-/

namespace Airbender.Blake2Round.Proofs

set_option maxHeartbeats 4000000

/-- First limb of the `d` word of column call `k` (prepared state lane `12 + k`). -/
def columnDLane : Nat → Nat
  | 0 => 198
  | 1 => 194
  | 2 => 200
  | _ => 196

def columnTrace {p : Nat} (k : Nat) (w : Nat → ZMod p) : GTrace p :=
  let v : Nat → ZMod p := fun i => w (256 + 40 * k + i)
  let aLo := w (155 + 4 * k)
  let aHi := w (157 + 4 * k)
  let bLo := w (171 + 4 * k)
  let bHi := w (173 + 4 * k)
  let cLo := w (186 + 2 * k)
  let cHi := w (187 + 2 * k)
  let dLo := w (columnDLane k)
  let dHi := w (columnDLane k + 1)
  let xLo := w (224 + 4 * k)
  let xHi := w (225 + 4 * k)
  let yLo := w (226 + 4 * k)
  let yHi := w (227 + 4 * k)
  let a1Lo := aLo + bLo + xLo - 65536 * v 1
  let a1Hi := aHi + bHi + xHi + v 1 - 65536 * v 3
  let c1Lo := cLo + (v 8 + 256 * v 9) - 65536 * v 12
  let c1Hi := cHi + (v 6 + 256 * v 7) + v 12 - 65536 * v 15
  let a2Lo := a1Lo + (v 22 + 128 * v 21) + yLo - 65536 * v 25
  let a2Hi := a1Hi + (v 23 + 128 * v 20) + yHi + v 25 - 65536 * v 27
  let c2Lo := c1Lo + (v 28 + 256 * v 31) - 65536 * v 33
  let c2Hi := c1Hi + (v 29 + 256 * v 30) + v 33 - 65536 * v 35
  { aLo := aLo, aHi := aHi, bLo := bLo, bHi := bHi, cLo := cLo, cHi := cHi,
    dLo := dLo, dHi := dHi, xLo := xLo, xHi := xHi, yLo := yLo, yHi := yHi,
    d0 := v 4, d1 := (-7864320 : ZMod p) * (dLo - v 4),
    d2 := v 5, d3 := (-7864320 : ZMod p) * (dHi - v 5),
    a1b0 := v 0, a1b1 := (-7864320 : ZMod p) * (a1Lo - v 0),
    a1b2 := v 2, a1b3 := (-7864320 : ZMod p) * (a1Hi - v 2),
    ka0 := v 1, ka1 := v 3, r0 := v 6, r1 := v 7, r2 := v 8, r3 := v 9,
    c3lo := v 10, c9lo := v 11, c4lo := (-491520 : ZMod p) * (c1Lo - (v 10 + 8 * v 11)),
    c3hi := v 13, c9hi := v 14, c4hi := (-491520 : ZMod p) * (c1Hi - (v 13 + 8 * v 14)),
    kc0 := v 12, kc1 := v 15,
    b3lo := v 16, b9lo := v 17, b4lo := (-491520 : ZMod p) * (bLo - (v 16 + 8 * v 17)),
    b3hi := v 18, b9hi := v 19, b4hi := (-491520 : ZMod p) * (bHi - (v 18 + 8 * v 19)),
    x9lo := v 20, x9hi := v 21, x7lo := v 22, x7hi := v 23,
    a2b0 := v 24, a2b1 := (-7864320 : ZMod p) * (a2Lo - v 24),
    a2b2 := v 26, a2b3 := (-7864320 : ZMod p) * (a2Hi - v 26),
    kb0 := v 25, kb1 := v 27, s0 := v 28, s1 := v 29, s2 := v 30, s3 := v 31,
    c2l0 := v 32, c2h0 := (-15728640 : ZMod p) * (c2Lo - v 32),
    c2l1 := v 34, c2h1 := (-15728640 : ZMod p) * (c2Hi - v 34),
    kd0 := v 33, kd1 := v 35, t0 := v 36, t1 := v 37, t2 := v 38, t3 := v 39,
    a2Lo := a2Lo, a2Hi := a2Hi, b2Lo := v 36 + 512 * v 39, b2Hi := v 37 + 512 * v 38,
    c2Lo := c2Lo, c2Hi := c2Hi, d2Lo := v 28 + 256 * v 31, d2Hi := v 29 + 256 * v 30 }

/-- An evaluated query column is the named field of a column trace. -/
macro "column_eq" : tactic => `(tactic| (
  simp only [columnTrace, columnDLane, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod]
  try mod_ring))

/-- The limb equations of a column call hold by construction, with BabyBear inverses. -/
theorem column_limbs {p : Nat} [Fact p.Prime] (compatible : 64 * (-31457280 : ZMod p) = 1)
    (k : Nat) (w : Nat → ZMod p) : (columnTrace k w).Limbs := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  constructor <;> simp only [columnTrace] <;> mod_ring

end Airbender.Blake2Round.Proofs
