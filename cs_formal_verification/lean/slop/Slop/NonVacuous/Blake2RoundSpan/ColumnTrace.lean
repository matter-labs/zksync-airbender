module
public import Slop.NonVacuous.Blake2RoundSpan.Columns
public import Slop.NonVacuous.Blake2RoundSpan.GHonest
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-! The trace of column G call `k` (`Blake2Round.Proofs.columnTrace`) at the honest assignment is the field record
    of the honest G row on the prepared lanes `k, 4 + k, 8 + k, 12 + k` and scheduled words `2k, 2k + 1`
    (`toTrace (x.colCall k)`): the allocated slots are its values, and every computed field (a quotient by a
    power of two, a sum with carries) is the cast of a natural-number identity of the G row's values. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Blake2Round.Proofs

/-- A computed field: the cast of the natural identity `e`, scaled by `C` (the inverse of the power of two). -/
scoped macro "field_identity " C:term:max e:term : tactic => `(tactic| (
  have identity := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e)
  push_cast at identity ⊢
  linear_combination (norm := ring_nf) ($C : ZMod 2013265921) * identity
  try reduce_mod_char))

/-- A natural identity of a G row's values, from their definitions. -/
scoped macro "g_identity" : tactic => `(tactic| (
  simp only [Blake2GSpan.RowInput.carryA0, Blake2GSpan.RowInput.carryA1, Blake2GSpan.RowInput.carryA2,
    Blake2GSpan.RowInput.carryA3, Blake2GSpan.RowInput.carryC0, Blake2GSpan.RowInput.carryC1,
    Blake2GSpan.RowInput.carryC2, Blake2GSpan.RowInput.carryC3, Blake2GSpan.RowInput.sumA0,
    Blake2GSpan.RowInput.sumA1, Blake2GSpan.RowInput.sumA2, Blake2GSpan.RowInput.sumA3,
    Blake2GSpan.RowInput.sumC0, Blake2GSpan.RowInput.sumC1, Blake2GSpan.RowInput.sumC2,
    Blake2GSpan.RowInput.sumC3, Blake2GSpan.RowInput.a1lo, Blake2GSpan.RowInput.a1hi,
    Blake2GSpan.RowInput.c1lo, Blake2GSpan.RowInput.c1hi, Blake2GSpan.RowInput.a2lo, Blake2GSpan.RowInput.a2hi,
    Blake2GSpan.RowInput.c2lo, Blake2GSpan.RowInput.c2hi, Blake2GSpan.RowInput.b1lo, Blake2GSpan.RowInput.b1hi,
    Blake2GSpan.RowInput.d1lo, Blake2GSpan.RowInput.d1hi, Blake2GSpan.RowInput.d2lo, Blake2GSpan.RowInput.d2hi,
    Blake2GSpan.RowInput.b2lo, Blake2GSpan.RowInput.b2hi]
  omega))

variable {p : Nat} [Fact p.Prime]

theorem column_trace (hp : p = 2013265921) (x : RowInput) {k : Nat} (hk : k < 4) :
    columnTrace k (x.assignment (p := p)) = toTrace (x.colCall k) := by
  subst hp
  have aLo : x.assignment (p := 2013265921) (155 + 4 * k) = ((x.colCall k).a.lo : ZMod _) :=
    x.assignment_laneLo (by omega)
  have aHi : x.assignment (p := 2013265921) (157 + 4 * k) = ((x.colCall k).a.hi : ZMod _) :=
    x.assignment_laneHi (by omega)
  have bLo : x.assignment (p := 2013265921) (171 + 4 * k) = ((x.colCall k).b.lo : ZMod _) := x.assignment_laneLo' hk
  have bHi : x.assignment (p := 2013265921) (173 + 4 * k) = ((x.colCall k).b.hi : ZMod _) := x.assignment_laneHi' hk
  have cLo : x.assignment (p := 2013265921) (186 + 2 * k) = ((x.colCall k).c.lo : ZMod _) := x.assignment_suffixLo hk
  have cHi : x.assignment (p := 2013265921) (187 + 2 * k) = ((x.colCall k).c.hi : ZMod _) := x.assignment_suffixHi hk
  have dLo : x.assignment (p := 2013265921) (columnDLane k) = ((x.colCall k).d.lo : ZMod _) :=
    x.assignment_dLaneLo hk
  have dHi : x.assignment (p := 2013265921) (columnDLane k + 1) = ((x.colCall k).d.hi : ZMod _) :=
    x.assignment_dLaneHi hk
  have xLo : x.assignment (p := 2013265921) (224 + 4 * k) = ((x.colCall k).mx.lo : ZMod _) := by
    have := x.assignment_schedLo (p := 2013265921) (j := 2 * k) (by omega)
    rwa [show 224 + 2 * (2 * k) = 224 + 4 * k by ring] at this
  have xHi : x.assignment (p := 2013265921) (225 + 4 * k) = ((x.colCall k).mx.hi : ZMod _) := by
    have := x.assignment_schedHi (p := 2013265921) (j := 2 * k) (by omega)
    rwa [show 224 + 2 * (2 * k) + 1 = 225 + 4 * k by ring] at this
  have yLo : x.assignment (p := 2013265921) (226 + 4 * k) = ((x.colCall k).my.lo : ZMod _) := by
    have := x.assignment_schedLo (p := 2013265921) (j := 2 * k + 1) (by omega)
    rwa [show 224 + 2 * (2 * k + 1) = 226 + 4 * k by ring] at this
  have yHi : x.assignment (p := 2013265921) (227 + 4 * k) = ((x.colCall k).my.hi : ZMod _) := by
    have := x.assignment_schedHi (p := 2013265921) (j := 2 * k + 1) (by omega)
    rwa [show 224 + 2 * (2 * k + 1) + 1 = 227 + 4 * k by ring] at this
  unfold columnTrace toTrace
  simp (disch := omega) only [aLo, aHi, bLo, bHi, cLo, cHi, dLo, dHi, xLo, xHi, yLo, yHi,
    RowInput.assignment_colSlot, RowInput.colSlot]
  generalize x.colCall k = g
  congr 1
  · field_identity (-7864320) (show g.d.lo = g.d.lo % 256 + 256 * (g.d.lo / 256) by omega)
  · field_identity (-7864320) (show g.d.hi = g.d.hi % 256 + 256 * (g.d.hi / 256) by omega)
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
  · field_identity (-7864320) (show g.a.lo + g.b.lo + g.mx.lo + g.xb2 + 16 * g.xb3 + 128 * g.xb4 + g.my.lo =
      65536 * g.carryA0 + 65536 * g.carryA2 + g.a2lo % 256 + 256 * (g.a2lo / 256) by g_identity)
  · field_identity (-7864320) (show g.a.hi + g.b.hi + g.mx.hi + g.carryA0 + g.xb5 + 16 * g.xb0 + 128 * g.xb1 +
      g.my.hi + g.carryA2 = 65536 * g.carryA1 + 65536 * g.carryA3 + g.a2hi % 256 + 256 * (g.a2hi / 256) by
      g_identity)
  · field_identity (-15728640) (show g.c.lo + g.xd2 + 256 * g.xd3 + g.xe1 + 256 * g.xe2 =
      65536 * g.carryC0 + 65536 * g.carryC2 + g.c2lo % 128 + 128 * (g.c2lo / 128) by g_identity)
  · field_identity (-15728640) (show g.c.hi + g.xd0 + 256 * g.xd1 + g.carryC0 + g.xe3 + 256 * g.xe0 + g.carryC2 =
      65536 * g.carryC1 + 65536 * g.carryC3 + g.c2hi % 128 + 128 * (g.c2hi / 128) by g_identity)
  · field_identity 1 (show g.a.lo + g.b.lo + g.mx.lo + g.xb2 + 16 * g.xb3 + 128 * g.xb4 + g.my.lo =
      65536 * g.carryA0 + 65536 * g.carryA2 + g.a2lo by g_identity)
  · field_identity 1 (show g.a.hi + g.b.hi + g.mx.hi + g.carryA0 + g.xb5 + 16 * g.xb0 + 128 * g.xb1 +
      g.my.hi + g.carryA2 = 65536 * g.carryA1 + 65536 * g.carryA3 + g.a2hi by g_identity)
  · field_identity 1 (show g.xf1 + 512 * g.xf2 = g.b2lo from rfl)
  · field_identity 1 (show g.xf3 + 512 * g.xf0 = g.b2hi from rfl)
  · field_identity 1 (show g.c.lo + g.xd2 + 256 * g.xd3 + g.xe1 + 256 * g.xe2 =
      65536 * g.carryC0 + 65536 * g.carryC2 + g.c2lo by g_identity)
  · field_identity 1 (show g.c.hi + g.xd0 + 256 * g.xd1 + g.carryC0 + g.xe3 + 256 * g.xe0 + g.carryC2 =
      65536 * g.carryC1 + 65536 * g.carryC3 + g.c2hi by g_identity)
  · field_identity 1 (show g.xe1 + 256 * g.xe2 = g.d2lo from rfl)
  · field_identity 1 (show g.xe3 + 256 * g.xe0 = g.d2hi from rfl)

end Airbender.NonVacuous.Blake2RoundSpan
