import Slop.Blake2G.CallPhysical
import Human.Trace.Workers.Blake2G.WorkVector
import Slop.Delegation.ReverseFold

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] Specs.BLAKE3.g
set_option backward.isDefEq.respectTransparency false

theorem physical_reference_step (reduced : Bool) (call : Nat) {before after : State}
    {state message : BitVec 32}
    (correct : Blake2G.State.spec (physicalInput (controllerAt reduced call) before state message)
      (physicalWords after state)) :
    (physicalWords after state).map Word.value = WorkVector.step reduced call
      (physicalWords before message) ((physicalWords before state).map Word.value) := by
  let controller := controllerAt reduced call
  have stateIndex (index : Fin 4) :
      Fin.ofNat 16 (Control.step controller).stateOffsets[index] = (stateLanes controller)[index] := by
    apply Fin.ext
    simp only [Fin.val_ofNat, stateLanes, Fin.getElem_fin, Vector.getElem_ofFn]
    exact Nat.mod_eq_of_lt (Control.Proofs.state_offsets_bounded controller index)
  have messageIndex (index : Fin 2) :
      (physicalWords before message)[Fin.ofNat 16 (Control.step controller).messageOffsets[index]] =
        (physicalWords before message)[(Control.step controller).messageOffsets[index]]'
          (Control.Proofs.message_offsets_bounded controller index) := by
    have bounded := Control.Proofs.message_offsets_bounded controller index
    simp only [Fin.getElem_fin] at bounded
    simp only [Fin.getElem_fin, Fin.val_ofNat, Nat.mod_eq_of_lt bounded]
  dsimp only [controller] at stateIndex messageIndex
  unfold Blake2G.State.spec at correct
  dsimp only [physicalInput] at correct
  dsimp only [WorkVector.step]
  rw [stateIndex 0, stateIndex 1, stateIndex 2, stateIndex 3]
  apply correct.trans
  apply congrArg₂
  · exact congrArg Word.value (messageIndex 0).symm
  · exact congrArg Word.value (messageIndex 1).symm

theorem call_workvector [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (after : State),
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ cell ∈ cells, ∃ value, cell.read after = .ok value after) ∧
      physicalWords after messagePointer = physicalWords initial messagePointer ∧
      (physicalWords after statePointer).map Word.value = WorkVector.run reduced
        (physicalWords initial statePointer) (physicalWords initial messagePointer) := by
  obtain ⟨statePointer, messagePointer, after, states, count, stateRead, messageRead,
    head, last, trace, readable, effects⟩ := call_physical_steps hp inverse accepted inputs aligned
  have endpoints : states[0]'(by omega) = after ∧ states[data.rows.length]'(by omega) = initial := by
    constructor
    · have first := head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
      exact Option.some.inj first
    · have finish := List.getLast_of_getLast?_eq_some last
      simpa only [List.getLast_eq_getElem, count, Nat.add_sub_cancel] using finish
  let physical : Fin (data.rows.length + 1) → Vector Nat 16 :=
    fun i => (physicalWords (states[i.val]'(by omega)) statePointer).map Word.value
  let message : Fin (data.rows.length + 1) → Vector Word 16 :=
    fun i => physicalWords (states[i.val]'(by omega)) messagePointer
  have unchanged := reverse_constant message (fun i => (effects i).2)
  have transitions : ∀ i : Fin data.rows.length,
      physical ⟨i.val, by omega⟩ = WorkVector.step reduced (data.rows.length - 1 - i.val)
        (message ⟨data.rows.length, by omega⟩) (physical ⟨i.val + 1, by omega⟩) := by
    intro i
    have current := physical_reference_step reduced (data.rows.length - 1 - i.val) (effects i).1
    rw [show physicalWords (states[i.val + 1]'(by omega)) messagePointer =
      message ⟨data.rows.length, by omega⟩ from unchanged ⟨i.val + 1, by omega⟩] at current
    exact current
  have result := reverse_fold physical
    (fun call state => WorkVector.step reduced call (message ⟨data.rows.length, by omega⟩) state) transitions
  refine ⟨statePointer, messagePointer, after, stateRead, messageRead, trace, ?_, ?_, ?_⟩
  · simpa only [endpoints.1] using readable 0 (by omega)
  · simpa only [message, endpoints.1, endpoints.2] using unchanged ⟨0, by omega⟩
  · have folded : (physicalWords after statePointer).map Word.value =
        Fin.foldl data.rows.length (fun state i => WorkVector.step reduced i.val
          (physicalWords initial messagePointer) state) ((physicalWords initial statePointer).map Word.value) := by
      simpa only [physical, message, endpoints.1, endpoints.2] using result
    have countEq := congrArg (fun n => Fin.foldl n
      (fun state i => WorkVector.step reduced i.val (physicalWords initial messagePointer) state)
      ((physicalWords initial statePointer).map Word.value)) inputs.calls
    exact folded.trans countEq

end Airbender.Blake2G.Proofs
