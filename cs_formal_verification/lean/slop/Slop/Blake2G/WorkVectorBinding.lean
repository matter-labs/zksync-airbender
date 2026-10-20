import Slop.Blake2G.CallWorkVector
import Slop.Blake2Round.CompressionBinding

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem workvector_binding_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : State) (statePointer messagePointer : BitVec 32) (input message output : Vector Word 16),
      WorkVector.WordMapping initial after statePointer messagePointer input message output ∧
        Delegation.TraceMapping data initial after cells ∧
        output.map Word.value = WorkVector.run reduced input message := by
  obtain ⟨statePointer, messagePointer, after, stateRead, messageRead, trace, afterReadable, messageSame, result⟩ :=
    call_workvector hp inverse accepted inputs aligned
  obtain ⟨state, msg, stateRead', messageRead', _, _, _, tracked⟩ := call_block_domain hp inverse accepted inputs
  have sameState := (EStateM.Result.ok.inj (stateRead.symm.trans stateRead')).1
  have sameMessage := (EStateM.Result.ok.inj (messageRead.symm.trans messageRead')).1
  subst state
  subst msg
  have initialReadable := boundary_readable inputs.memory
  have stateTracked : ∀ i : Fin 16, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    simpa only [if_true, Nat.zero_add] using tracked true i
  have messageTracked : ∀ i : Fin 16, Cell.ram (messagePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    simpa only [Bool.false_eq_true, if_false, Nat.zero_add] using tracked false i
  refine ⟨after, statePointer, messagePointer, physicalWords initial statePointer,
    physicalWords initial messagePointer, physicalWords after statePointer, ?_, trace, result⟩
  refine ⟨⟨stateRead, messageRead⟩, Blake2Round.Proofs.block_at stateTracked initialReadable,
    Blake2Round.Proofs.block_at messageTracked initialReadable,
    Blake2Round.Proofs.block_at stateTracked afterReadable, ?_⟩
  have final := Blake2Round.Proofs.block_at messageTracked afterReadable
  change Blake2Round.Compression.WordsAt after messagePointer 0 (physicalWords after messagePointer) at final
  rw [messageSame] at final
  exact final

theorem workvector_binding [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (after : State) (statePointer messagePointer : BitVec 32) (input message output : Vector Word 16),
      WorkVector.WordMapping initial after statePointer messagePointer input message output ∧
        Delegation.TraceMapping data initial after cells ∧
        output.map Word.value = WorkVector.run reduced input message :=
  workvector_binding_at_boundary hp inverse accepted inputs.toBoundaryInputs aligned

end Airbender.Blake2G.Proofs
