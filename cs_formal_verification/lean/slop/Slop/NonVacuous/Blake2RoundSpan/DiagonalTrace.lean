module
public import Slop.NonVacuous.Blake2RoundSpan.ColumnTrace

@[expose] public section

/-! The trace of diagonal G call `k` (`Blake2Round.Proofs.diagonalTrace`) at the honest assignment is the field
    record of the honest G row on the lanes after the column step (`toTrace (x.diagCall k)`): its inputs are the
    column calls' outputs, its outputs the written extended state, and every computed field is the cast of a
    natural-number identity of the G row's values. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Blake2Round.Proofs

/-- A computed field from two natural identities, scaled by `C₁` and `C₂`. -/
scoped macro "field_identity2 " C1:term:max e1:term:max C2:term:max e2:term : tactic => `(tactic| (
  have first := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e1)
  have second := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e2)
  push_cast at first second ⊢
  linear_combination (norm := ring_nf) ($C1 : ZMod 2013265921) * first + ($C2 : ZMod 2013265921) * second
  try reduce_mod_char))

/-- A computed field from four natural identities. -/
scoped macro "field_identity4 " C1:term:max e1:term:max C2:term:max e2:term:max C3:term:max e3:term:max C4:term:max
    e4:term : tactic => `(tactic| (
  have first := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e1)
  have second := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e2)
  have third := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e3)
  have fourth := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e4)
  push_cast at first second third fourth ⊢
  linear_combination (norm := ring_nf) ($C1 : ZMod 2013265921) * first + ($C2 : ZMod 2013265921) * second +
    ($C3 : ZMod 2013265921) * third + ($C4 : ZMod 2013265921) * fourth
  try reduce_mod_char))

variable {p : Nat} [Fact p.Prime]

theorem diagonal_trace (hp : p = 2013265921) (x : RowInput) {k : Nat} (hk : k < 4)
    (valid : GValid (x.colCall ((k + 3) % 4))) :
    diagonalTrace k (x.assignment (p := p)) = toTrace (x.diagCall k) := by
  subst hp
  have xLo : x.assignment (p := 2013265921) (240 + 4 * k) = ((x.diagCall k).mx.lo : ZMod _) := by
    have := x.assignment_schedLo (p := 2013265921) (j := 8 + 2 * k) (by omega)
    rwa [show 224 + 2 * (8 + 2 * k) = 240 + 4 * k by ring] at this
  have xHi : x.assignment (p := 2013265921) (241 + 4 * k) = ((x.diagCall k).mx.hi : ZMod _) := by
    have := x.assignment_schedHi (p := 2013265921) (j := 8 + 2 * k) (by omega)
    rwa [show 224 + 2 * (8 + 2 * k) + 1 = 241 + 4 * k by ring] at this
  have yLo : x.assignment (p := 2013265921) (242 + 4 * k) = ((x.diagCall k).my.lo : ZMod _) := by
    have := x.assignment_schedLo (p := 2013265921) (j := 9 + 2 * k) (by omega)
    rwa [show 224 + 2 * (9 + 2 * k) = 242 + 4 * k by ring] at this
  have yHi : x.assignment (p := 2013265921) (243 + 4 * k) = ((x.diagCall k).my.hi : ZMod _) := by
    have := x.assignment_schedHi (p := 2013265921) (j := 9 + 2 * k) (by omega)
    rwa [show 224 + 2 * (9 + 2 * k) + 1 = 243 + 4 * k by ring] at this
  have a2Lo : x.assignment (p := 2013265921) (writeLane k) = ((x.diagCall k).a2lo : ZMod _) := by
    rw [writeLane, x.assignment_outLo (by omega), x.out_a hk]; rfl
  have a2Hi : x.assignment (p := 2013265921) (writeLane k + 1) = ((x.diagCall k).a2hi : ZMod _) := by
    rw [writeLane, x.assignment_outHi (by omega), x.out_a hk]; rfl
  have b2Lo : x.assignment (p := 2013265921) (writeLane (4 + (k + 1) % 4)) = ((x.diagCall k).b2lo : ZMod _) := by
    rw [writeLane, x.assignment_outLo (by omega), x.out_b hk]; rfl
  have b2Hi : x.assignment (p := 2013265921) (writeLane (4 + (k + 1) % 4) + 1) = ((x.diagCall k).b2hi : ZMod _) := by
    rw [writeLane, x.assignment_outHi (by omega), x.out_b hk]; rfl
  have c2Lo : x.assignment (p := 2013265921) (writeLane (8 + (k + 2) % 4)) = ((x.diagCall k).c2lo : ZMod _) := by
    rw [writeLane, x.assignment_outLo (by omega), x.out_c hk]; rfl
  have c2Hi : x.assignment (p := 2013265921) (writeLane (8 + (k + 2) % 4) + 1) = ((x.diagCall k).c2hi : ZMod _) := by
    rw [writeLane, x.assignment_outHi (by omega), x.out_c hk]; rfl
  have d2Lo : x.assignment (p := 2013265921) (writeLane (12 + (k + 3) % 4)) = ((x.diagCall k).d2lo : ZMod _) := by
    rw [writeLane, x.assignment_outLo (by omega), x.out_d hk]; rfl
  have d2Hi : x.assignment (p := 2013265921) (writeLane (12 + (k + 3) % 4) + 1) = ((x.diagCall k).d2hi : ZMod _) := by
    rw [writeLane, x.assignment_outHi (by omega), x.out_d hk]; rfl
  have aw : (x.colCall k).a2lo = (x.diagCall k).a.lo ∧ (x.colCall k).a2hi = (x.diagCall k).a.hi := by
    simp only [RowInput.diagCall, gCall, x.mixed_a hk]; exact ⟨rfl, rfl⟩
  have bw : (x.colCall ((k + 1) % 4)).b2lo = (x.diagCall k).b.lo ∧ (x.colCall ((k + 1) % 4)).b2hi = (x.diagCall k).b.hi := by
    simp only [RowInput.diagCall, gCall, x.mixed_b (k := (k + 1) % 4) (by omega)]; exact ⟨rfl, rfl⟩
  have cw : (x.colCall ((k + 2) % 4)).c2lo = (x.diagCall k).c.lo ∧ (x.colCall ((k + 2) % 4)).c2hi = (x.diagCall k).c.hi := by
    simp only [RowInput.diagCall, gCall, x.mixed_c (k := (k + 2) % 4) (by omega)]; exact ⟨rfl, rfl⟩
  have dw : (x.diagCall k).d = ⟨(x.colCall ((k + 3) % 4)).d2lo, (x.colCall ((k + 3) % 4)).d2hi⟩ := by
    simp only [RowInput.diagCall, gCall, x.mixed_d (k := (k + 3) % 4) (by omega)]; rfl
  unfold diagonalTrace
  rw [column_trace rfl x hk, column_trace rfl x (k := (k + 1) % 4) (by omega), column_trace rfl x (k := (k + 2) % 4) (by omega),
    column_trace rfl x (k := (k + 3) % 4) (by omega)]
  unfold toTrace
  simp (disch := omega) only [xLo, xHi, yLo, yHi, a2Lo, a2Hi, b2Lo, b2Hi, c2Lo, c2Hi, d2Lo, d2Hi, aw.1, aw.2, bw.1, bw.2, cw.1, cw.2, dw,
    RowInput.assignment_diagSlot, RowInput.diagSlot]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, xe0, xe1, xe2, xe3, -, -, -, -⟩ :=
    valid.xors
  generalize x.colCall ((k + 3) % 4) = c at xe0 xe1 xe2 xe3 ⊢
  generalize x.diagCall k = g
  simp only [GTrace.mk.injEq, true_and, and_true]
  and_intros
  · congr 1; simp only [Blake2GSpan.RowInput.d2lo]; omega
  · congr 1; simp only [Blake2GSpan.RowInput.d2lo]; omega
  · congr 1; simp only [Blake2GSpan.RowInput.d2hi]; omega
  · congr 1; simp only [Blake2GSpan.RowInput.d2hi]; omega
  · field_identity (-7864320) (show g.a.lo + g.b.lo + g.mx.lo =
      65536 * g.carryA0 + g.a1lo % 256 + 256 * (g.a1lo / 256) by g_identity)
  · field_identity (-7864320) (show g.a.hi + g.b.hi + g.mx.hi + g.carryA0 =
      65536 * g.carryA1 + g.a1hi % 256 + 256 * (g.a1hi / 256) by g_identity)
  · field_identity (-491520) (show g.c.lo + g.xd2 + 256 * g.xd3 =
      65536 * g.carryC0 + g.c1lo % 8 + 8 * (g.c1lo / 8 % 512) + 4096 * (g.c1lo / 4096) by g_identity)
  · field_identity (-491520) (show g.c.hi + g.xd0 + 256 * g.xd1 + g.carryC0 =
      65536 * g.carryC1 + g.c1hi % 8 + 8 * (g.c1hi / 8 % 512) + 4096 * (g.c1hi / 4096) by g_identity)
  · field_identity (-491520) (show g.b.lo = g.b.lo % 8 + 8 * (g.b.lo / 8 % 512) + 4096 * (g.b.lo / 4096) by omega)
  · field_identity (-491520) (show g.b.hi = g.b.hi % 8 + 8 * (g.b.hi / 8 % 512) + 4096 * (g.b.hi / 4096) by omega)
  · field_identity (-7864320) (show g.a2lo = g.a2lo % 256 + 256 * (g.a2lo / 256) by omega)
  · field_identity (-7864320) (show g.a2hi = g.a2hi % 256 + 256 * (g.a2hi / 256) by omega)
  · field_identity (-30720) (show g.a.lo + g.b.lo + g.mx.lo + g.xb2 + 16 * g.xb3 + 128 * g.xb4 + g.my.lo =
      65536 * g.carryA0 + 65536 * g.carryA2 + g.a2lo by g_identity)
  · field_identity2 (-30720 * -30720) (show g.a.lo + g.b.lo + g.mx.lo + g.xb2 + 16 * g.xb3 + 128 * g.xb4 + g.my.lo =
      65536 * g.carryA0 + 65536 * g.carryA2 + g.a2lo by g_identity) (-30720)
      (show g.a.hi + g.b.hi + g.mx.hi + g.carryA0 + g.xb5 + 16 * g.xb0 + 128 * g.xb1 + g.my.hi + g.carryA2 =
      65536 * g.carryA1 + 65536 * g.carryA3 + g.a2hi by g_identity)
  · field_identity (-7864320) (show g.d2hi = g.xe3 + 256 * g.xe0 from rfl)
  · field_identity (-7864320) (show g.d2lo = g.xe1 + 256 * g.xe2 from rfl)
  · field_identity (-15728640) (show g.c2lo = g.c2lo % 128 + 128 * (g.c2lo / 128) by omega)
  · field_identity (-15728640) (show g.c2hi = g.c2hi % 128 + 128 * (g.c2hi / 128) by omega)
  · field_identity2 (-30720) (show g.c.lo + g.xd2 + 256 * g.xd3 + g.xe1 + 256 * g.xe2 =
      65536 * g.carryC0 + 65536 * g.carryC2 + g.c2lo by g_identity) (-30720 * 256 * -7864320)
      (show g.d2lo = g.xe1 + 256 * g.xe2 from rfl)
  · field_identity4 (-30720 * -30720) (show g.c.lo + g.xd2 + 256 * g.xd3 + g.xe1 + 256 * g.xe2 =
      65536 * g.carryC0 + 65536 * g.carryC2 + g.c2lo by g_identity) (-30720 * -30720 * 256 * -7864320)
      (show g.d2lo = g.xe1 + 256 * g.xe2 from rfl) (-30720)
      (show g.c.hi + g.xd0 + 256 * g.xd1 + g.carryC0 + g.xe3 + 256 * g.xe0 + g.carryC2 =
      65536 * g.carryC1 + 65536 * g.carryC3 + g.c2hi by g_identity) (-30720 * 256 * -7864320)
      (show g.d2hi = g.xe3 + 256 * g.xe0 from rfl)
  · field_identity (-3932160) (show g.b2hi = g.xf3 + 512 * g.xf0 from rfl)
  · field_identity (-3932160) (show g.b2lo = g.xf1 + 512 * g.xf2 from rfl)

end Airbender.NonVacuous.Blake2RoundSpan
