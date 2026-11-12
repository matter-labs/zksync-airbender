module
public import Slop.NonVacuous.Blake2RoundSpan.Honest
public import Slop.Blake2Round.GTrace
public import Slop.Blake2Round.GWord

@[expose] public section

/-! One G invocation of the round circuit, honestly: the field record (`Blake2Round.Proofs.GTrace`) of a Blake2s G
    row's honest values (`Blake2GSpan.RowInput`), and its sixteen table facts (`GTrace.Rows`) for canonical input
    words. The round circuit splits the same values into its own chunks: the 8-bit XORs of `d` are those of the G
    row, the 12-bit rotation XORs `b` and `c₁` in 3/9/4-bit chunks with a split (4+3) XOR, and `c₂` splits 7/9. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Blake2Round.Proofs

/-- The field record of an honest G row. -/
def toTrace {p : Nat} (g : Blake2GSpan.RowInput) : GTrace p where
  aLo := g.a.lo
  aHi := g.a.hi
  bLo := g.b.lo
  bHi := g.b.hi
  cLo := g.c.lo
  cHi := g.c.hi
  dLo := g.d.lo
  dHi := g.d.hi
  xLo := g.mx.lo
  xHi := g.mx.hi
  yLo := g.my.lo
  yHi := g.my.hi
  d0 := (g.d.lo % 256 : Nat)
  d1 := (g.d.lo / 256 : Nat)
  d2 := (g.d.hi % 256 : Nat)
  d3 := (g.d.hi / 256 : Nat)
  a1b0 := (g.a1lo % 256 : Nat)
  a1b1 := (g.a1lo / 256 : Nat)
  a1b2 := (g.a1hi % 256 : Nat)
  a1b3 := (g.a1hi / 256 : Nat)
  ka0 := g.carryA0
  ka1 := g.carryA1
  r0 := g.xd0
  r1 := g.xd1
  r2 := g.xd2
  r3 := g.xd3
  c3lo := (g.c1lo % 8 : Nat)
  c9lo := (g.c1lo / 8 % 512 : Nat)
  c4lo := (g.c1lo / 4096 : Nat)
  c3hi := (g.c1hi % 8 : Nat)
  c9hi := (g.c1hi / 8 % 512 : Nat)
  c4hi := (g.c1hi / 4096 : Nat)
  kc0 := g.carryC0
  kc1 := g.carryC1
  b3lo := (g.b.lo % 8 : Nat)
  b9lo := (g.b.lo / 8 % 512 : Nat)
  b4lo := (g.b.lo / 4096 : Nat)
  b3hi := (g.b.hi % 8 : Nat)
  b9hi := (g.b.hi / 8 % 512 : Nat)
  b4hi := (g.b.hi / 4096 : Nat)
  x9lo := g.xb1
  x9hi := g.xb4
  x7lo := (g.xb2 + 16 * g.xb3 : Nat)
  x7hi := (g.xb5 + 16 * g.xb0 : Nat)
  a2b0 := (g.a2lo % 256 : Nat)
  a2b1 := (g.a2lo / 256 : Nat)
  a2b2 := (g.a2hi % 256 : Nat)
  a2b3 := (g.a2hi / 256 : Nat)
  kb0 := g.carryA2
  kb1 := g.carryA3
  s0 := g.xe1
  s1 := g.xe3
  s2 := g.xe0
  s3 := g.xe2
  c2l0 := (g.c2lo % 128 : Nat)
  c2h0 := (g.c2lo / 128 : Nat)
  c2l1 := (g.c2hi % 128 : Nat)
  c2h1 := (g.c2hi / 128 : Nat)
  kd0 := g.carryC2
  kd1 := g.carryC3
  t0 := g.xf1
  t1 := g.xf3
  t2 := g.xf0
  t3 := g.xf2
  a2Lo := g.a2lo
  a2Hi := g.a2hi
  b2Lo := g.b2lo
  b2Hi := g.b2hi
  c2Lo := g.c2lo
  c2Hi := g.c2hi
  d2Lo := g.d2lo
  d2Hi := g.d2hi

/-- The canonical input words of a G call. -/
structure GValid (g : Blake2GSpan.RowInput) : Prop where
  a : g.a.Bounded
  b : g.b.Bounded
  c : g.c.Bounded
  d : g.d.Bounded
  mx : g.mx.Bounded
  my : g.my.Bounded

namespace GValid
variable {g : Blake2GSpan.RowInput} (valid : GValid g)
include valid

/-- The chunk widths of every XOR (`Blake2GSpan.RowInput.Valid.xors`; the G row's other inputs do not enter). -/
theorem xors :
    g.xd0 < 256 ∧ g.xd1 < 256 ∧ g.xd2 < 256 ∧ g.xd3 < 256 ∧ g.xb0 < 8 ∧ g.xb1 < 512 ∧ g.xb2 < 16 ∧ g.xb3 < 8 ∧
      g.xb4 < 512 ∧ g.xb5 < 16 ∧ g.xe0 < 256 ∧ g.xe1 < 256 ∧ g.xe2 < 256 ∧ g.xe3 < 256 ∧ g.xf0 < 128 ∧
      g.xf1 < 512 ∧ g.xf2 < 128 ∧ g.xf3 < 512 :=
  Blake2GSpan.RowInput.Valid.xors (x := gCall g.a g.b g.c g.d g.mx g.my)
    ⟨show 0 < 256 by decide, show Word.Bounded ⟨0, 0⟩ ∧ 0 % 64 = 0 by simp [Word.Bounded, limbBase],
      show Word.Bounded ⟨0, 0⟩ ∧ 0 % 64 = 0 by simp [Word.Bounded, limbBase], valid.a, valid.b, valid.c, valid.d, valid.mx, valid.my,
      fun _ => show 0 < 1 + 2 by decide, show 1 % 4 = 1 by decide, show 1 + 2 < Trace.timestampBase by decide⟩

/-- The honest carries: below 3, and Boolean for the two `c` additions. -/
theorem carries : g.carryA0 < 3 ∧ g.carryA1 < 3 ∧ g.carryA2 < 3 ∧ g.carryA3 < 3 ∧ g.carryC0 ≤ 1 ∧ g.carryC1 ≤ 1 ∧
    g.carryC2 ≤ 1 ∧ g.carryC3 ≤ 1 := by
  have a := valid.a
  have b := valid.b
  have c := valid.c
  have d := valid.d
  have mx := valid.mx
  have my := valid.my
  simp only [Word.Bounded, limbBase] at a b c d mx my
  obtain ⟨xd0, xd1, xd2, xd3, xb0, xb1, xb2, xb3, xb4, xb5, xe0, xe1, xe2, xe3, -, -, -, -⟩ :=
    valid.xors
  simp only [Blake2GSpan.RowInput.carryA0, Blake2GSpan.RowInput.carryA1, Blake2GSpan.RowInput.carryA2,
    Blake2GSpan.RowInput.carryA3, Blake2GSpan.RowInput.carryC0, Blake2GSpan.RowInput.carryC1,
    Blake2GSpan.RowInput.carryC2, Blake2GSpan.RowInput.carryC3, Blake2GSpan.RowInput.sumA0,
    Blake2GSpan.RowInput.sumA1, Blake2GSpan.RowInput.sumA2, Blake2GSpan.RowInput.sumA3,
    Blake2GSpan.RowInput.sumC0, Blake2GSpan.RowInput.sumC1, Blake2GSpan.RowInput.sumC2,
    Blake2GSpan.RowInput.sumC3, Blake2GSpan.RowInput.a1lo, Blake2GSpan.RowInput.a1hi, Blake2GSpan.RowInput.c1lo,
    Blake2GSpan.RowInput.c1hi, Blake2GSpan.RowInput.b1lo, Blake2GSpan.RowInput.b1hi, Blake2GSpan.RowInput.d1lo,
    Blake2GSpan.RowInput.d1hi, Blake2GSpan.RowInput.d2lo, Blake2GSpan.RowInput.d2hi]
  omega

/-- The written words are canonical. -/
theorem outputs : g.a2lo < 65536 ∧ g.a2hi < 65536 ∧ g.b2lo < 65536 ∧ g.b2hi < 65536 ∧ g.c2lo < 65536 ∧
    g.c2hi < 65536 ∧ g.d2lo < 65536 ∧ g.d2hi < 65536 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, xe0, xe1, xe2, xe3, xf0, xf1, xf2, xf3⟩ :=
    valid.xors
  simp only [Blake2GSpan.RowInput.a2lo, Blake2GSpan.RowInput.a2hi, Blake2GSpan.RowInput.b2lo,
    Blake2GSpan.RowInput.b2hi, Blake2GSpan.RowInput.c2lo, Blake2GSpan.RowInput.c2hi, Blake2GSpan.RowInput.d2lo,
    Blake2GSpan.RowInput.d2hi]
  omega

end GValid

variable {p : Nat} [Fact p.Prime]

/-- A chunk XOR of small natural numbers, read back from the field. -/
theorem chunkXor_cast (room : 65536 ≤ p) {w m n k : Nat} (hm : m < 2 ^ w) (hn : n < 2 ^ w) (hw : 2 ^ w ≤ 65536)
    (e : k = m ^^^ n) :
    ChunkXor w ((m : Nat) : ZMod p).val ((n : Nat) : ZMod p).val ((k : Nat) : ZMod p).val := by
  subst e
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.xor_lt_two_pow hm hn) hw) room)]
  exact ⟨hm, hn, rfl⟩

/-- The sixteen table facts of an honest G row. -/
theorem toTrace_rows (room : 65536 ≤ p) {g : Blake2GSpan.RowInput} (valid : GValid g) :
    (toTrace (p := p) g).Rows := by
  have a := valid.a
  have b := valid.b
  have c := valid.c
  have d := valid.d
  have mx := valid.mx
  have my := valid.my
  simp only [Word.Bounded, limbBase] at a b c d mx my
  obtain ⟨xd0, xd1, xd2, xd3, xb0, xb1, xb2, xb3, xb4, xb5, xe0, xe1, xe2, xe3, xf0, xf1, xf2, xf3⟩ :=
    valid.xors
  obtain ⟨ka0, ka1, kb0, kb1, kc0, kc1, kd0, kd1⟩ := valid.carries
  have a1lo : g.a1lo < 65536 := Nat.mod_lt _ (by decide)
  have a1hi : g.a1hi < 65536 := Nat.mod_lt _ (by decide)
  have c1lo : g.c1lo < 65536 := Nat.mod_lt _ (by decide)
  have c1hi : g.c1hi < 65536 := Nat.mod_lt _ (by decide)
  have a2lo : g.a2lo < 65536 := Nat.mod_lt _ (by decide)
  have a2hi : g.a2hi < 65536 := Nat.mod_lt _ (by decide)
  have c2lo : g.c2lo < 65536 := Nat.mod_lt _ (by decide)
  have c2hi : g.c2hi < 65536 := Nat.mod_lt _ (by decide)
  have val {n : Nat} (h : n < 65536) : ((n : Nat) : ZMod p).val = n := ZMod.val_natCast_of_lt (by omega)
  have chunk {w m n k : Nat} (hm : m < 2 ^ w) (hn : n < 2 ^ w) (hw : 2 ^ w ≤ 65536) (e : k = m ^^^ n) :=
    chunkXor_cast (p := p) room hm hn hw e
  have split {m n u v : Nat} (hm : m < 16) (hn : n < 8) (hu : u < 16) (hv : v < 8) :
      SplitXor ((m : Nat) : ZMod p).val ((n : Nat) : ZMod p).val ((u : Nat) : ZMod p).val
        ((v : Nat) : ZMod p).val (((m ^^^ u) + 16 * (n ^^^ v) : Nat) : ZMod p).val := by
    have x1 : m ^^^ u < 16 := Nat.xor_lt_two_pow (n := 4) hm hu
    have x2 : n ^^^ v < 8 := Nat.xor_lt_two_pow (n := 3) hn hv
    rw [val (by omega), val (by omega), val (by omega), val (by omega), val (by omega)]
    exact ⟨hm, hn, hu, hv, (split_xor hm hu).symm⟩
  refine
    { q0 := chunk (w := 8) (by omega) (by omega) (by decide) rfl
      q1 := chunk (w := 8) (by omega) (by omega) (by decide) rfl
      q2 := chunk (w := 8) (by omega) (by omega) (by decide) rfl
      q3 := chunk (w := 8) (by omega) (by omega) (by decide) rfl
      ka0 := by simp only [toTrace]; rw [val (by omega)]; exact ka0
      ka1 := by simp only [toTrace]; rw [val (by omega)]; exact ka1
      q4 := chunk (w := 9) (by omega) (by omega) (by decide) rfl
      q5 := chunk (w := 9) (by omega) (by omega) (by decide) rfl
      q6 := split (by omega) (by omega) (by omega) (by omega)
      q7 := split (by omega) (by omega) (by omega) (by omega)
      kc0 := by simp only [toTrace]; rw [val (by omega)]; omega
      kc1 := by simp only [toTrace]; rw [val (by omega)]; omega
      q8 := chunk (w := 8) xd3 (by omega) (by decide) rfl
      q9 := chunk (w := 8) xd1 (by omega) (by decide) rfl
      q10 := chunk (w := 8) xd2 (by omega) (by decide) rfl
      q11 := chunk (w := 8) xd0 (by omega) (by decide) rfl
      kb0 := by simp only [toTrace]; rw [val (by omega)]; exact kb0
      kb1 := by simp only [toTrace]; rw [val (by omega)]; exact kb1
      q12 := chunk (w := 9) xb4 (by omega) (by decide) rfl
      q13 := chunk (w := 9) xb1 (by omega) (by decide) rfl
      q14 := chunk (w := 7) (by omega) (by omega) (by decide) rfl
      q15 := chunk (w := 7) (by omega) (by omega) (by decide)
        (by unfold Blake2GSpan.RowInput.xf2; rw [Nat.add_comm (16 * _)])
      kd0 := by simp only [toTrace]; rw [val (by omega)]; omega
      kd1 := by simp only [toTrace]; rw [val (by omega)]; omega }

end Airbender.NonVacuous.Blake2RoundSpan
