import Slop.UnifiedReduced.Observation
import Slop.UnifiedReduced.ArithmeticExecution

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem observe_arithmetic {w : Nat → ZMod p} {before : State} {instruction : SailRV32.instruction} {input : Input}
    (observed : observe w before instruction = some (.arithmetic input)) :
    instruction = arithmeticInstruction input ∧ input.before = before ∧
      (∀ _index : (match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)),
        WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w) := by
  unfold observe at observed
  split at observed <;> simp only [Option.some.injEq, Observation.arithmetic.injEq,
    Observation.noConfusion] at observed
  all_goals first | contradiction | skip
  all_goals subst input
  all_goals refine ⟨?_, rfl, fun index => ?_⟩
  all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, index, rfl, rfl, rfl, rfl⟩

theorem observe_jump {w : Nat → ZMod p} {before : State} {instruction : SailRV32.instruction} {input : Jump.Input}
    (observed : observe w before instruction = some (.jump input)) :
    instruction = Jump.instruction input ∧ input.before = before ∧
      Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
  unfold observe at observed
  split at observed <;> simp at observed
  all_goals subst input
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem observe_branch {w : Nat → ZMod p} {before : State} {instruction : SailRV32.instruction} {input : Control.Branch.Input}
    (observed : observe w before instruction = some (.branch input)) :
    instruction = Control.Branch.instruction input ∧ input.before = before ∧
      Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
  unfold observe at observed
  split at observed <;> simp at observed
  all_goals subst input
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem observe_comparison {w : Nat → ZMod p} {before : State} {instruction : SailRV32.instruction} {input : Control.Comparison.Input}
    (observed : observe w before instruction = some (.comparison input)) :
    instruction = Control.Comparison.instruction input ∧ input.before = before ∧
      Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
  unfold observe at observed
  split at observed <;> simp at observed
  all_goals subst input
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem observe_binary {w : Nat → ZMod p} {before : State} {instruction : SailRV32.instruction}
    {shift : Bool} {input : Binary.Input}
    (observed : observe w before instruction = some (.binary shift input)) :
    (if shift then Shift.instruction input else Binary.instruction input) = some instruction ∧ input.before = before ∧
      Binary.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
  unfold observe at observed
  split at observed <;> simp at observed
  all_goals obtain ⟨rfl, rfl⟩ := observed
  all_goals refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals dsimp only [Binary.instruction, Shift.instruction]
  all_goals first | rfl | skip
  all_goals rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  all_goals simp

theorem observe_memory {w : Nat → ZMod p} {before : State} {instruction : SailRV32.instruction} {input : Airbender.WordMemory.Input}
    (observed : observe w before instruction = some (.memory input)) :
    instruction = (if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) ∧ input.before = before ∧
      WordMemory.WordMapping input
        ⟨⟨(w (if input.store then 44 else 38)).val, (w (if input.store then 45 else 39)).val⟩,
          Control.destination w, Control.finalPC w⟩ w := by
  unfold observe at observed
  split at observed <;> simp at observed
  all_goals subst input
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Airbender.UnifiedReduced.Proofs
