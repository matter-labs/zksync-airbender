import Slop.Blake2Round.GWord
import Slop.Blake2G.Soundness

set_option warningAsError true

/-!
One G invocation of the wider-table round, as field values: inputs, the chunks,
carries and XOR results of its sixteen table queries, and its outputs. Column
and diagonal invocations fill the same record (`ColumnTrace`, `DiagonalTrace`).
`GTrace.sound` derives Clean's G function from the chunk facts and limb equations.
-/

namespace Airbender.Blake2Round.Proofs

open Arithmetic

set_option maxHeartbeats 4000000

/-- XOR of two `width`-bit chunks, as one table row states it. -/
def ChunkXor (width a b c : Nat) : Prop := a < 2 ^ width ∧ b < 2 ^ width ∧ c = a ^^^ b

/-- The split 4+3 XOR row: `out = (b4 ^ c4) | ((b3 ^ c3) << 4)`. -/
def SplitXor (b4 b3 c4 c3 out : Nat) : Prop :=
  b4 < 16 ∧ b3 < 8 ∧ c4 < 16 ∧ c3 < 8 ∧ out = (b4 ^^^ c4) ||| ((b3 ^^^ c3) <<< 4)

/-- Field values of one G invocation. Names follow the circuit: `a1`/`a2` are
    the two additions into `a` (bytes `a1b*`, `a2b*`, carries `ka*`, `kb*`),
    `r*`/`s*` the byte XORs of the two `d` rotations, `c3*`/`c9*`/`c4*` the
    3/9/4-bit chunks of the first `c` sum (carries `kc*`), `b3*`/`b9*`/`b4*`
    those of `b`, `x9*`/`x7*` the rotate-12 XORs, `c2l*`/`c2h*` the 7/9-bit
    chunks of the second `c` sum (carries `kd*`), `t*` the rotate-7 XORs. -/
structure GTrace (p : Nat) where
  aLo : ZMod p
  aHi : ZMod p
  bLo : ZMod p
  bHi : ZMod p
  cLo : ZMod p
  cHi : ZMod p
  dLo : ZMod p
  dHi : ZMod p
  xLo : ZMod p
  xHi : ZMod p
  yLo : ZMod p
  yHi : ZMod p
  d0 : ZMod p
  d1 : ZMod p
  d2 : ZMod p
  d3 : ZMod p
  a1b0 : ZMod p
  a1b1 : ZMod p
  a1b2 : ZMod p
  a1b3 : ZMod p
  ka0 : ZMod p
  ka1 : ZMod p
  r0 : ZMod p
  r1 : ZMod p
  r2 : ZMod p
  r3 : ZMod p
  c3lo : ZMod p
  c9lo : ZMod p
  c4lo : ZMod p
  c3hi : ZMod p
  c9hi : ZMod p
  c4hi : ZMod p
  kc0 : ZMod p
  kc1 : ZMod p
  b3lo : ZMod p
  b9lo : ZMod p
  b4lo : ZMod p
  b3hi : ZMod p
  b9hi : ZMod p
  b4hi : ZMod p
  x9lo : ZMod p
  x9hi : ZMod p
  x7lo : ZMod p
  x7hi : ZMod p
  a2b0 : ZMod p
  a2b1 : ZMod p
  a2b2 : ZMod p
  a2b3 : ZMod p
  kb0 : ZMod p
  kb1 : ZMod p
  s0 : ZMod p
  s1 : ZMod p
  s2 : ZMod p
  s3 : ZMod p
  c2l0 : ZMod p
  c2h0 : ZMod p
  c2l1 : ZMod p
  c2h1 : ZMod p
  kd0 : ZMod p
  kd1 : ZMod p
  t0 : ZMod p
  t1 : ZMod p
  t2 : ZMod p
  t3 : ZMod p
  a2Lo : ZMod p
  a2Hi : ZMod p
  b2Lo : ZMod p
  b2Hi : ZMod p
  c2Lo : ZMod p
  c2Hi : ZMod p
  d2Lo : ZMod p
  d2Hi : ZMod p

/-- The sixteen table rows of one invocation, as chunk facts. -/
structure GTrace.Rows {p : Nat} (t : GTrace p) : Prop where
  q0 : ChunkXor 8 t.d0.val t.a1b0.val t.r0.val
  q1 : ChunkXor 8 t.d1.val t.a1b1.val t.r1.val
  q2 : ChunkXor 8 t.d2.val t.a1b2.val t.r2.val
  q3 : ChunkXor 8 t.d3.val t.a1b3.val t.r3.val
  ka0 : t.ka0.val < 3
  ka1 : t.ka1.val < 3
  q4 : ChunkXor 9 t.b9lo.val t.c9lo.val t.x9lo.val
  q5 : ChunkXor 9 t.b9hi.val t.c9hi.val t.x9hi.val
  q6 : SplitXor t.b4lo.val t.b3hi.val t.c4lo.val t.c3hi.val t.x7lo.val
  q7 : SplitXor t.b4hi.val t.b3lo.val t.c4hi.val t.c3lo.val t.x7hi.val
  kc0 : t.kc0.val < 3
  kc1 : t.kc1.val < 3
  q8 : ChunkXor 8 t.r3.val t.a2b1.val t.s0.val
  q9 : ChunkXor 8 t.r1.val t.a2b3.val t.s1.val
  q10 : ChunkXor 8 t.r2.val t.a2b0.val t.s2.val
  q11 : ChunkXor 8 t.r0.val t.a2b2.val t.s3.val
  kb0 : t.kb0.val < 3
  kb1 : t.kb1.val < 3
  q12 : ChunkXor 9 t.x9hi.val t.c2h0.val t.t0.val
  q13 : ChunkXor 9 t.x9lo.val t.c2h1.val t.t1.val
  q14 : ChunkXor 7 t.x7lo.val t.c2l0.val t.t2.val
  q15 : ChunkXor 7 t.x7hi.val t.c2l1.val t.t3.val
  kd0 : t.kd0.val < 3
  kd1 : t.kd1.val < 3

/-- The limb equations of one invocation: chunk splits and sums with carries. -/
structure GTrace.Limbs {p : Nat} (t : GTrace p) : Prop where
  dLo : t.dLo = t.d0 + 256 * t.d1
  dHi : t.dHi = t.d2 + 256 * t.d3
  a1Lo : t.aLo + t.bLo + t.xLo = t.a1b0 + 256 * t.a1b1 + 65536 * t.ka0
  a1Hi : t.aHi + t.bHi + t.xHi + t.ka0 = t.a1b2 + 256 * t.a1b3 + 65536 * t.ka1
  bLo : t.bLo = t.b3lo + 8 * t.b9lo + 4096 * t.b4lo
  bHi : t.bHi = t.b3hi + 8 * t.b9hi + 4096 * t.b4hi
  c1Lo : t.cLo + (t.r2 + 256 * t.r3) = t.c3lo + 8 * t.c9lo + 4096 * t.c4lo + 65536 * t.kc0
  c1Hi : t.cHi + (t.r0 + 256 * t.r1) + t.kc0 =
    t.c3hi + 8 * t.c9hi + 4096 * t.c4hi + 65536 * t.kc1
  a2Lo' : (t.a1b0 + 256 * t.a1b1) + (t.x7lo + 128 * t.x9hi) + t.yLo =
    t.a2b0 + 256 * t.a2b1 + 65536 * t.kb0
  a2Hi' : (t.a1b2 + 256 * t.a1b3) + (t.x7hi + 128 * t.x9lo) + t.yHi + t.kb0 =
    t.a2b2 + 256 * t.a2b3 + 65536 * t.kb1
  c2Lo' : (t.c3lo + 8 * t.c9lo + 4096 * t.c4lo) + (t.s0 + 256 * t.s3) =
    t.c2l0 + 128 * t.c2h0 + 65536 * t.kd0
  c2Hi' : (t.c3hi + 8 * t.c9hi + 4096 * t.c4hi) + (t.s1 + 256 * t.s2) + t.kd0 =
    t.c2l1 + 128 * t.c2h1 + 65536 * t.kd1
  outALo : t.a2Lo = t.a2b0 + 256 * t.a2b1
  outAHi : t.a2Hi = t.a2b2 + 256 * t.a2b3
  outBLo : t.b2Lo = t.t0 + 512 * t.t3
  outBHi : t.b2Hi = t.t1 + 512 * t.t2
  outCLo : t.c2Lo = t.c2l0 + 128 * t.c2h0
  outCHi : t.c2Hi = t.c2l1 + 128 * t.c2h1
  outDLo : t.d2Lo = t.s0 + 256 * t.s3
  outDHi : t.d2Hi = t.s1 + 256 * t.s2

/-- What the sixteen queries and the limb equations state about one invocation. -/
structure GTrace.Facts {p : Nat} (t : GTrace p) : Prop extends t.Rows, t.Limbs

def GTrace.input {p : Nat} (t : GTrace p) : Blake2G.Input :=
  ⟨⟨⟨t.aLo.val, t.aHi.val⟩, ⟨t.bLo.val, t.bHi.val⟩, ⟨t.cLo.val, t.cHi.val⟩,
    ⟨t.dLo.val, t.dHi.val⟩⟩, ⟨t.xLo.val, t.xHi.val⟩, ⟨t.yLo.val, t.yHi.val⟩⟩

def GTrace.output {p : Nat} (t : GTrace p) : Blake2G.Words :=
  ⟨⟨t.a2Lo.val, t.a2Hi.val⟩, ⟨t.b2Lo.val, t.b2Hi.val⟩, ⟨t.c2Lo.val, t.c2Hi.val⟩,
    ⟨t.d2Lo.val, t.d2Hi.val⟩⟩

/-- A field equation between small natural combinations holds over `Nat`. -/
theorem nat_of_field {p : Nat} [Fact p.Prime] {x y : ZMod p} (field : x = y) {L R : Nat}
    (hx : (L : ZMod p) = x) (hy : (R : ZMod p) = y) (hL : L < p) (hR : R < p) : L = R := by
  have := congrArg ZMod.val (hx.trans (field.trans hy.symm))
  rwa [ZMod.val_natCast_of_lt hL, ZMod.val_natCast_of_lt hR] at this

/-- `nat_eq e` proves the `Nat` form of the field equation `e`. -/
macro "nat_eq " e:term : tactic => `(tactic| (
  refine nat_of_field $e ?_ ?_ ?_ ?_
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]; try ring
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]; try ring
  · first | exact ZMod.val_lt _ | omega
  · first | exact ZMod.val_lt _ | omega))

theorem ChunkXor.out {width a b c : Nat} (h : ChunkXor width a b c) : c < 2 ^ width :=
  h.2.2 ▸ Nat.xor_lt_two_pow h.1 h.2.1

/-- All four outputs are 16-bit limbs, from the chunk bounds of the queries. -/
theorem GTrace.output_bounded {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {t : GTrace p}
    (f : t.Facts) :
    t.output.a.Bounded ∧ t.output.b.Bounded ∧ t.output.c.Bounded ∧ t.output.d.Bounded := by
  have a0 : t.a2b0.val < 256 := f.q10.2.1
  have a1 : t.a2b1.val < 256 := f.q8.2.1
  have a2 : t.a2b2.val < 256 := f.q11.2.1
  have a3 : t.a2b3.val < 256 := f.q9.2.1
  have s0 : t.s0.val < 256 := f.q8.out
  have s1 : t.s1.val < 256 := f.q9.out
  have s2 : t.s2.val < 256 := f.q10.out
  have s3 : t.s3.val < 256 := f.q11.out
  have t0 : t.t0.val < 512 := f.q12.out
  have t1 : t.t1.val < 512 := f.q13.out
  have t2 : t.t2.val < 128 := f.q14.out
  have t3 : t.t3.val < 128 := f.q15.out
  have c0 : t.c2l0.val < 128 := f.q14.2.1
  have c1 : t.c2h0.val < 512 := f.q12.2.1
  have c2 : t.c2l1.val < 128 := f.q15.2.1
  have c3 : t.c2h1.val < 512 := f.q13.2.1
  have aL : t.a2Lo.val = t.a2b0.val + 256 * t.a2b1.val := by nat_eq f.outALo
  have aH : t.a2Hi.val = t.a2b2.val + 256 * t.a2b3.val := by nat_eq f.outAHi
  have bL : t.b2Lo.val = t.t0.val + 512 * t.t3.val := by nat_eq f.outBLo
  have bH : t.b2Hi.val = t.t1.val + 512 * t.t2.val := by nat_eq f.outBHi
  have cL : t.c2Lo.val = t.c2l0.val + 128 * t.c2h0.val := by nat_eq f.outCLo
  have cH : t.c2Hi.val = t.c2l1.val + 128 * t.c2h1.val := by nat_eq f.outCHi
  have dL : t.d2Lo.val = t.s0.val + 256 * t.s3.val := by nat_eq f.outDLo
  have dH : t.d2Hi.val = t.s1.val + 256 * t.s2.val := by nat_eq f.outDHi
  simp only [GTrace.output, Word.Bounded, limbBase]
  omega

end Airbender.Blake2Round.Proofs
