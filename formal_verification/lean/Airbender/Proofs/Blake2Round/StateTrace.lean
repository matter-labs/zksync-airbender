import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.StateTransport
import Airbender.Proofs.Delegation.CallBoundaries

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem call_state_trace [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (ascending : List (Delegation.Row p)),
    ∃ count : ascending.length = data.rows.length,
    ∃ (after : State) (states : List State), ∃ stateCount : states.length = data.rows.length + 1,
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧ ascending.Perm data.rows ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ (i : Nat) (bound : i < states.length), ∀ cell ∈ cells,
        ∃ value, cell.read (states[i]'bound) = .ok value (states[i]'bound)) ∧
      ∀ i : Fin data.rows.length,
        let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
        ∃ round : Fin 10, round.val = data.rows.length - 1 - i.val ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment) ∧
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          SailHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          ∀ index : Fin 40,
            let address := if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
              else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))
            ramWord (states[i.val + 1]'(by omega)) address =
              ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).readWord
                (wordIndex index)).value ∧
            ramWord (states[i.val]'(by omega)) address =
              ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).writtenWord
                (wordIndex index)).value := by
  obtain ⟨ascending, after, permutation, _, controls, _, history, effects, terminal⟩ :=
    call_scheduled_history hp inverse accepted inputs aligned
  have count := permutation.length_eq
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨states, stateCount, head, last, readable, ports⟩ :=
    grouped_atomic_boundaries clockBound accepted inputs.memory reversedPerm history aligned
  have stateLength : states.length = data.rows.length + 1 := by
    simpa only [List.length_reverse, count] using stateCount
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, pointers, _, _⟩ :=
    call_pointers clockBound accepted inputs
  have bounds := operation_word_bounds_at_boundary hp inverse accepted (call_operation_inputs clockBound accepted inputs)
  have trace := grouped_trace_mapping reversedPerm history terminal
  refine ⟨statePointer, messagePointer, ascending, count, after, states, stateLength,
    stateRead, messageRead, permutation, head, last, trace, readable, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have index : row = ascending[data.rows.length - 1 - i.val]'(by omega) := by
    simp only [row, List.getElem_reverse, count]
  have control := (controls (data.rows.length - 1 - i.val) (by omega)).1
  have high := congrArg Word.hi control
  have limit : data.rows.length ≤ 10 := by rw [inputs.calls]; split_ifs <;> decide
  let round : Fin 10 := ⟨data.rows.length - 1 - i.val, by omega⟩
  have power : 2 ^ round.val < 1024 := by have := round.isLt; interval_cases round.val <;> decide
  have read : (row.assignment Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val := by
    simpa [← index, readToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.readCode, WordColumns.code, pairCode, controlAt, round,
      Nat.mod_eq_of_lt power, Variables.controlReadHi] using high
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints setupTable) := by
    have holds := accepted.constraints row member
    simp only [Delegation.Row.constraints, inputs.family row member, inputs.tables,
      Delegation.modeledSetup] at holds
    exact Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
  obtain ⟨chosen, mask, effect⟩ := effects row member
  have actualMask := exclusive_mask (by norm_num [timestampBase] at clockBound; omega) core flags round read
  have same : chosen = round := by
    have one := actualMask chosen
    rw [mask chosen, if_pos rfl] at one
    by_contra different
    rw [if_neg different] at one
    exact one_ne_zero one
  subst chosen
  obtain ⟨events, eventPerm, current, observed⟩ := ports i.val (by simpa only [List.length_reverse, count] using i.isLt)
  refine ⟨round, rfl, effect, events, eventPerm, current, ?_⟩
  intro index
  have native : row = ⟨.blakeRound, row.assignment⟩ := by
    have native : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [inputs.family row member] using native
  have reads : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by
    simpa only [← native] using bounds.reads row member
  have writes : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using bounds.writes row member
  have actual : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.read (states[i.val + 1]'(by omega)) =
          .ok (memoryWord (port.readCode row.assignment)) (states[i.val + 1]'(by omega)) ∧
        cell.read (states[i.val]'(by omega)) =
          .ok (memoryWord (port.writeCode row.assignment)) (states[i.val]'(by omega)) := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := observed port (by simpa only [← native] using present)
    exact ⟨cell, code, read, written⟩
  have result := native_word_observations effect.2.2.2 reads writes actual index
  have pointer := pointers row member round
  simpa only [Addresses.expected, Fin.getElem_fin, Vector.getElem_ofFn,
    pointer.1, pointer.2, Word.ofBitVec_roundtrip] using result

end Airbender.Blake2Round.Proofs
