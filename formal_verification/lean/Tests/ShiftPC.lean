import Tests.ShiftHistoryRows
import Airbender.Proofs.ShiftBinop.PC

namespace Tests.ShiftPC
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Airbender Arithmetic Verification ShiftBinop

/-- Two actual native carry-gadget edges: low-limb carry and full RV32 wrap.
    All non-PC columns and native lookup queries retain the accepted SLL row. -/
def wrapAssignment (full : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 65532 else if i = 1 then (if full then 65535 else 65534) else
  if i = 13 ∨ i = 61 then 0 else if i = 14 then (if full then 0 else 65535) else
  if i = 62 then 1 else if i = 63 then (if full then 0 else -1) else
  if i = 64 then (if full then 1 else 0) else
    ShiftHistoryRows.assignment ⟨0,by decide⟩ i

/-- Both boundary fixtures satisfy every native equation and lookup; the PC
    gate proof is tested on complete imported rows, not a relaxed fragment. -/
theorem native_constraints (full : Bool) : FlatOperation.ConstraintsHoldFlat
    (environment (wrapAssignment full)) ShiftBinop.importedConstraints := by
  cases full <;>
    simp [ShiftBinop.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
      environment,wrapAssignment,ShiftHistoryRows.assignment,ShiftRoutingWitness.assignment,
      ShiftRoutingWitness.values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide) | skip
  all_goals apply ShiftRoutingWitness.tagged_query_contains
  all_goals first
    | simpa [Expression.eval,environment,wrapAssignment,ShiftHistoryRows.assignment] using
        ShiftRoutingQueries.lookup_members ⟨0,by decide⟩ ⟨0,by decide⟩
    | simpa [Expression.eval,environment,wrapAssignment,ShiftHistoryRows.assignment] using
        ShiftRoutingQueries.lookup_members ⟨0,by decide⟩ ⟨1,by decide⟩
    | simpa [Expression.eval,environment,wrapAssignment,ShiftHistoryRows.assignment] using
        ShiftRoutingQueries.lookup_members ⟨0,by decide⟩ ⟨2,by decide⟩
    | simpa [Expression.eval,environment,wrapAssignment,ShiftHistoryRows.assignment] using
        ShiftRoutingQueries.lookup_members ⟨0,by decide⟩ ⟨3,by decide⟩

/-- The exact same native theorem used for original retirement derives bounds
    and modular +4 at both carry edges. -/
theorem native_successor (full : Bool) :
    (Word.mk (wrapAssignment full 13).val (wrapAssignment full 14).val).Bounded ∧
    (Word.mk (wrapAssignment full 13).val (wrapAssignment full 14).val).toBitVec =
      (Word.mk (wrapAssignment full 0).val (wrapAssignment full 1).val).toBitVec + 4 :=
  ShiftBinop.Proofs.native_pc_successor (by decide) (native_constraints full)
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩
    (by cases full <;> constructor <;> decide +kernel) (by cases full <;> decide +kernel)

theorem wrapped_values :
    (Word.mk (wrapAssignment false 0).val (wrapAssignment false 1).val).toBitVec = 0xfffefffc ∧
    (Word.mk (wrapAssignment false 13).val (wrapAssignment false 14).val).toBitVec = 0xffff0000 ∧
    (Word.mk (wrapAssignment true 0).val (wrapAssignment true 1).val).toBitVec = 0xfffffffc ∧
    (Word.mk (wrapAssignment true 13).val (wrapAssignment true 14).val).toBitVec = 0 := by
  decide +kernel

end Tests.ShiftPC
