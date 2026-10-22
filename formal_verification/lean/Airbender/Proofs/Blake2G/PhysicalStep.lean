import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.PhysicalWords

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem physical_state_step [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p} {state message : BitVec 32} {before after : State}
    {cells : List Cell} {events : List MemoryAccess}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1) (controlBound : (w Variables.controlReadLo).val < 256)
    (addresses : Addresses.spec
      ⟨⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩,
        Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after)
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (distinct : state ≠ message)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (tracked : ∀ «block» : Bool, ∀ word : Fin 16,
      Cell.ram ((if «block» then state else message) + BitVec.ofNat 32 (4 * word.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    let controller : Control.Input := ⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩
    Blake2G.State.spec (physicalInput controller before state message) (physicalWords after state) ∧
      physicalWords after message = physicalWords before message := by
  let controller : Control.Input := ⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩
  have encoded := native_encoded_words controller addresses reads writes observed
  obtain ⟨inputWords, outputWords⟩ := physical_mixing_words controller encoded
  let input := physicalInput controller before state message
  let output := physicalWords after state
  have mapping : Blake2G.State.Mapping input output w := by
    constructor
    · change WordMapping (Blake2G.State.mixingInput (physicalInput controller before state message))
        (Blake2G.State.mixingOutput (physicalInput controller before state message) (physicalWords after state)) w
      rw [inputWords, outputWords]
      exact Native.Proofs.native_mapping w
    · intro index
      let controlOutput : Control.Output :=
        ⟨⟨(w Variables.controlWriteLo).val, (w Variables.controlWriteHi).val⟩,
          Variables.stateOffsetColumns.map (fun column => (w column).val),
          Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
      have controlMapping : Control.Mapping controller controlOutput w := ⟨rfl, active, rfl⟩
      have enforced := Control.Proofs.soundness (by omega) controller controlOutput w ⟨core, controlMapping⟩
      have equal := congrArg (fun value : Control.Output => value.stateOffsets[index]) enforced
      fin_cases index <;> simpa [input, physicalInput, stateLanes, controlOutput] using equal
  have frame («block» : Bool) (word : Fin 16)
      (untouched : «block» = true → ∀ lane : Fin 4,
        (Control.step controller).stateOffsets[lane] ≠ word.val) :=
    native_block_frame controller addresses stateAligned messageAligned distinct history permutation
      aligned tracked readable «block» word untouched
  have interfaces : Blake2G.State.InterfaceAssumptions input output w := by
    refine ⟨active, controlBound, ?_, ?_⟩
    · constructor
      all_goals simp only [input, physicalInput, Blake2G.State.mixingInput, stateLanes,
        physicalWords, Blake2Round.Proofs.blockWords, Fin.getElem_fin, Vector.getElem_ofFn, ramEncoding]
      all_goals exact Word.ofBitVec_bound _
    · intro word untouched
      have absent : ∀ lane : Fin 4, (Control.step controller).stateOffsets[lane] ≠ word.val := by
        intro lane equal
        apply untouched lane
        apply Fin.ext
        simpa [input, physicalInput, stateLanes] using equal.symm
      simpa [input, output, physicalInput, physicalWords, Blake2Round.Proofs.blockWords] using
        frame true word (fun _ => absent)
  refine ⟨Blake2G.State.Proofs.soundness (by omega) inverse input output w ⟨interfaces, core, mapping⟩, ?_⟩
  apply Vector.ext
  intro i bound
  simpa [physicalWords, Blake2Round.Proofs.blockWords] using
    frame false ⟨i, bound⟩ (fun equal => by cases equal)

end Airbender.Blake2G.Proofs
