import Airbender.Proofs.Blake2G.PhysicalStep
import Airbender.Proofs.Blake2G.StateTrace

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem call_physical_steps [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (after : State) (states : List State),
    ∃ count : states.length = data.rows.length + 1,
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ (i : Nat) (bound : i < states.length), ∀ cell ∈ cells,
        ∃ value, cell.read (states[i]'bound) = .ok value (states[i]'bound)) ∧
      ∀ i : Fin data.rows.length,
        let controller := scheduledController reduced (data.rows.length - 1 - i.val) (by rw [← inputs.calls]; omega)
        Blake2G.State.spec
          (physicalInput controller (states[i.val + 1]'(by omega)) statePointer messagePointer)
          (physicalWords (states[i.val]'(by omega)) statePointer) ∧
          physicalWords (states[i.val]'(by omega)) messagePointer =
            physicalWords (states[i.val + 1]'(by omega)) messagePointer := by
  obtain ⟨ascending, ascendingCount, after, states, count, permutation, head, last, trace, readable, effects⟩ :=
    call_state_trace hp inverse accepted inputs aligned
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, stateAligned, messageAligned, separate, tracked⟩ :=
    call_block_domain hp inverse accepted inputs
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨state, message, stateRead', messageRead', pointers, _, _⟩ := call_pointers clockBound accepted inputs
  have sameState := (EStateM.Result.ok.inj (stateRead.symm.trans stateRead')).1
  have sameMessage := (EStateM.Result.ok.inj (messageRead.symm.trans messageRead')).1
  subst state
  subst message
  have operations : Delegation.OperationInputs data initial cells Keccak.Controller.rows := by
    refine ⟨inputs.memory, inputs.tables, ?_, ?_⟩
    all_goals intro row member other; have := inputs.family row member; simp_all
  have bounds := operation_word_bounds hp inverse accepted operations
  refine ⟨statePointer, messagePointer, after, states, count, stateRead, messageRead,
    head, last, trace, readable, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, ascendingCount] using i.isLt)
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have family := inputs.family row member
  have native : row = ⟨.blakeG, row.assignment⟩ := by
    have same : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [family] using same
  obtain ⟨_, control, events, eventPerm, history, ports⟩ := effects i
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints (setupTable Control.controllerRows)) := by
    have h := accepted.constraints row member
    simp only [Delegation.Row.constraints, family, inputs.tables, Delegation.modeledSetup] at h
    exact Verification.holds_of_sublist h (List.sublist_append_left _ importedConstraintsTimestampLookups)
  have value := congrArg Word.lo control
  have controlValue : (row.assignment Variables.controlReadLo).val =
      (controlAt reduced (data.rows.length - 1 - i.val)).lo := by
    simpa [row, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode,
      WordColumns.code, WordColumns.evaluate, Variables.controlReadLo] using value
  have callBound : data.rows.length - 1 - i.val < callCount reduced := by rw [← inputs.calls]; omega
  have controlBound : (row.assignment Variables.controlReadLo).val < 256 := by
    rw [controlValue]
    exact (scheduledController reduced _ callBound).register.isLt
  have reads : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by simpa only [← native] using bounds.reads row member
  have writes : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using bounds.writes row member
  have addresses := native_addresses (by omega) inverse core (inputs.active row member) controlBound reads
  have fixed : addressInput row.assignment controlBound =
      ⟨⟨⟨(row.assignment Variables.controlReadLo).val, controlBound⟩, true⟩,
        Word.ofBitVec statePointer, Word.ofBitVec messagePointer⟩ := by
    dsimp only [addressInput]
    rw [(pointers row member).1, (pointers row member).2]
  rw [fixed] at addresses
  have observed : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.read (states[i.val + 1]'(by omega)) =
          .ok (memoryWord (port.readCode row.assignment)) (states[i.val + 1]'(by omega)) ∧
        cell.read (states[i.val]'(by omega)) =
          .ok (memoryWord (port.writeCode row.assignment)) (states[i.val]'(by omega)) := by
    intro port present
    obtain ⟨cell, _, code, read, write⟩ := ports port (by simpa only [← native] using present)
    exact ⟨cell, code, read, write⟩
  have controller : (⟨⟨(row.assignment Variables.controlReadLo).val, controlBound⟩, true⟩ : Control.Input) =
      scheduledController reduced (data.rows.length - 1 - i.val) callBound := by
    congr 1
    exact Fin.ext controlValue
  have current := physical_state_step hp inverse core (inputs.active row member) controlBound addresses reads writes
    observed stateAligned messageAligned separate history
    (by simpa only [← native] using eventPerm) aligned tracked (readable (i.val + 1) (by omega))
  simpa only [controller] using current

end Airbender.Blake2G.Proofs
