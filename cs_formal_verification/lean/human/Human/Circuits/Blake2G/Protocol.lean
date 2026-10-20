import Human.Circuits.Blake2G.Control

namespace Airbender.Blake2G
open Trace

/-- The pinned G-only caller performs eight G operations per round, over
    seven reduced rounds or ten full rounds. -/
def callCount (reduced : Bool) : Nat := if reduced then 56 else 80

/-- Expected x12 after `i` calls. Bit seven selects reduced rounds; the
    counter returns to zero after the complete request. Later control words
    are derived from imported lookups and initialized matching. -/
def controlAt (reduced : Bool) (i : Nat) : Arithmetic.Word :=
  ⟨(if reduced then 128 else 0) + i % callCount reduced, 0⟩

/-- The pinned caller's control word for one G position, independent of
    the witness. The counter is wrapped to the public span of seven or ten rounds. -/
def controllerAt (reduced : Bool) (call : Nat) : Control.Input :=
  ⟨⟨(controlAt reduced call).lo, by
    have bound : call % callCount reduced < callCount reduced :=
      Nat.mod_lt _ (by cases reduced <;> decide)
    cases reduced <;> simp only [controlAt, callCount, Bool.false_eq_true, ↓reduceIte] at * <;> omega⟩, true⟩

end Airbender.Blake2G
