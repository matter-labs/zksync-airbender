import Airbender.Review.Delegation.Requests
import Airbender.Proofs.Constraints

namespace Airbender.Delegation.Requests.Proofs
open Trace
set_option warningAsError true

private theorem zero_fields [Fact p.Prime] {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      AddSub.importedConstraints) (selected : w 17 = 1) :
    w 29 = 0 ∧ w 30 = 0 ∧ w 27 = 0 ∧ w 28 = 0 ∧ w 33 = 0 ∧ w 34 = 0 := by
  have a := Verification.assertion_of_holds constraints ⟨6, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
  have b := Verification.assertion_of_holds constraints ⟨7, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
  have c := Verification.assertion_of_holds constraints ⟨8, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
  have d := Verification.assertion_of_holds constraints ⟨9, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
  have e := Verification.assertion_of_holds constraints ⟨10, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
  have f := Verification.assertion_of_holds constraints ⟨11, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
  simp [AddSub.importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at a b c d e f
  exact ⟨a, b, c, d, e, f⟩

theorem caller_tokens [Fact p.Prime] {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      AddSub.importedConstraints) (selected : w 17 = 1) :
    readToken w AddSub.importedConstraintsMemoryPorts[1] = (caller w).empty ∧
    writeToken AddSub.importedConstraintsTraceColumns w AddSub.importedConstraintsMemoryPorts[1] =
      (caller w).issued ∧ w 33 = 0 ∧ w 34 = 0 := by
  obtain ⟨lo, hi, timeLo, timeHi, resultLo, resultHi⟩ := zero_fields constraints selected
  simp [caller, callerPort, AddSub.importedConstraintsDecoderColumns, Request.issued, Request.empty, Request.token, AddSub.importedConstraintsMemoryPorts,
    AddSub.importedConstraintsTraceColumns, readToken, writeToken, MemoryAddress.code,
    MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
    rawPair, lo, hi, timeLo, timeHi, resultLo, resultHi]
  decide

private theorem issued_injective : Function.Injective (Request.issued (p := p)) := by
  intro a b equal
  have address := congrArg MemoryToken.address equal
  have time := congrArg MemoryToken.time equal
  simp only [Request.issued, Request.token, Nat.pair_eq_pair] at address time
  cases a
  cases b
  simp_all

theorem nonzero_matching {calls fulfillments : List (Request p)}
    (matching : Matching calls fulfillments) :
    (calls.filter (fun r => decide (Live r))).Perm
      (fulfillments.filter (fun r => decide (Live r))) := by
  have filtered := matching.filter (fun token => decide (token.time ≠ (0, 0)))
  have emptyFilter (requests : List (Request p)) :
      (requests.map Request.empty).filter (fun token => decide (token.time ≠ (0, 0))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro token member
    obtain ⟨request, _, rfl⟩ := List.mem_map.mp member
    simp [Request.empty, Request.token]
  simp only [List.filter_append, emptyFilter, List.append_nil, List.nil_append] at filtered
  have result : ((calls.filter (fun r => decide (Live r))).map Request.issued).Perm
      ((fulfillments.filter (fun r => decide (Live r))).map Request.issued) := by
    simp only [List.filter_map] at filtered
    convert filtered using 1 <;> congr 2
  exact (List.map_perm_map_iff issued_injective).mp result

theorem zero_time_fulfillment_invisible (address : Nat) :
    Matching ([] : List (Request p)) [⟨address, (0, 0)⟩] := by
  simp [Matching, Request.issued, Request.empty, Request.token]

end Airbender.Delegation.Requests.Proofs
