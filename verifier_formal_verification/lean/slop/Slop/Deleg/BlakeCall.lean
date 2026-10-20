import Slop.Deleg.Calls

/-! The Blake2s round function (CSR `0x7c7`), 7 rounds, any mode: one call (`blakeRound_mode_call`). -/

namespace RV
open Spec
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- The control word before round `r`: 7 rounds, the node on the right (`right`), compression mode (`comp`). -/
def bCtl (right comp : Bool) (r : Nat) : Word :=
  (BitVec.ofNat 32 (1 + (if right then 2 else 0) + (if comp then 4 else 0)) <<< 16) ||| (1#32 <<< (r + 19))

/-- The block the rounds mix in. -/
def bMsg (right comp : Bool) (h : Vector Word 8) (m : Vector Word 16) : Vector Word 16 :=
  if comp then
    (if right then Vector.ofFn fun i : Fin 16 => if i.val < 8 then m[i.val % 16] else h[(i.val - 8) % 8]
     else Vector.ofFn fun i : Fin 16 => if i.val < 8 then h[i.val % 8] else m[(i.val - 8) % 16])
  else m

/-- The working vector round 0 starts from. -/
def bV0 (comp : Bool) (h : Vector Word 8) (e : Vector Word 16) : Vector Word 16 :=
  if comp then
    #v[configuredIV 0, configuredIV 1, configuredIV 2, configuredIV 3, configuredIV 4, configuredIV 5,
      configuredIV 6, configuredIV 7, IV 0, IV 1, IV 2, IV 3, IV 4 ^^^ 64#32, IV 5, IV 6 ^^^ 0xFFFFFFFF#32, IV 7]
  else blakeV0 h e

/-- The state the last round folds the working vector into. -/
def bH0 (comp : Bool) (h : Vector Word 8) : Vector Word 8 := if comp then Vector.ofFn configuredIV else h

theorem blakeRound_mode_call (mem : Word → BitVec 8) (p q : Word) (hp : Buffer p 96 128) (hq : Buffer q 64 64)
    (hpq : p ≠ q) (right comp : Bool) (r : Nat) (h7 : r < 7) :
    let h := readWords mem p 8
    let e := readWords mem (p + 32#32) 16
    let v' := round (bMsg right comp h (readWords mem q 16)) (SIGMA ⟨r, by omega⟩) (if r = 0 then bV0 comp h e else e)
    Delegation.blakeRound p q (bCtl right comp r) mem = some
      { writes := writesAt p (if r = 6 then blakeFinal (bH0 comp h) v' else h) ++ writesAt (p + 32#32) v',
        reg := 12, val := bCtl right comp (r + 1) } := by
  intro h e v'
  obtain ⟨hp1, hp2, -⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  cases right <;> cases comp <;> interval_cases r
  all_goals
    simp only [Delegation.blakeRound, bCtl, hp1, hp2, hq1, hq2, hq3, ne_eq, hpq, not_false_eq_true, true_and]
    simp (config := { decide := true }) only [ite_true, ite_false]
  all_goals
    simp only [v', h, e, bV0, bMsg, bH0, blakeV0, blakeFinal, Option.some.injEq, Effect.mk.injEq, ite_true,
      ite_false, and_true, show (p + 32 : Word) = p + 32#32 from rfl, Bool.false_eq_true]
    refine ⟨?_, by decide⟩
    congr

end RV
