import Airbender.Review.Helpers.Delegation.Requests
import Airbender.Proofs.AddSub.Selectors

namespace Airbender.Delegation.Requests.Proofs
open Trace
set_option warningAsError true

theorem caller_tokens [Fact p.Prime] {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      AddSub.importedConstraints) (selected : w 17 = 1) :
    readToken w AddSub.importedConstraintsMemoryPorts[1] = (caller w).empty ∧
    writeToken AddSub.importedConstraintsTraceColumns w AddSub.importedConstraintsMemoryPorts[1] =
      (caller w).issued ∧ w 33 = 0 ∧ w 34 = 0 := by
  obtain ⟨lo, hi, timeLo, timeHi, resultLo, resultHi⟩ := AddSub.Proofs.delegation_zeroes constraints selected
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

theorem shifted_times_unique {α : Type} {rows : List α}
    {request : α → Request p} {rank : α → Nat}
    (unique : (rows.map rank).Nodup)
    (values : ∀ row ∈ rows, (timeOfPair (request row).time).value = rank row + 1) :
    (rows.map (fun row => (request row).time)).Nodup := by
  have valueUnique : (rows.map fun row => (timeOfPair (request row).time).value).Nodup := by
    have equal : (rows.map fun row => (timeOfPair (request row).time).value) =
        rows.map (fun row => rank row + 1) := List.map_congr_left values
    rw [equal]
    apply List.pairwise_map.mpr
    exact (List.pairwise_map.mp unique).imp (by
      intro first last different same
      exact different (Nat.add_right_cancel same))
  apply List.pairwise_map.mpr
  exact (List.pairwise_map.mp valueUnique).imp (by
    intro first last different same
    exact different (congrArg (fun time => (timeOfPair time).value) same))

theorem bounded_pool [Fact p.Prime] {calls fulfillments : List (Request p)}
    (matching : Matching calls fulfillments)
    (clocks : ∀ call ∈ calls, (timeOfPair call.time).Bounded ∧ Live call ∧
      (timeOfPair call.time).lo + 2 < timestampBase)
    (unique : (calls.map Request.time).Nodup) :
    calls.Perm (fulfillments.filter (fun request => decide (Live request))) ∧
    (∀ worker ∈ fulfillments, (timeOfPair worker.time).Bounded ∧
      (timeOfPair worker.time).lo + 2 < timestampBase) ∧
    ((fulfillments.filter (fun request => decide (Live request))).map Request.time).Nodup := by
  have allCalls : calls.filter (fun request => decide (Live request)) = calls := by
    apply List.filter_eq_self.mpr
    exact fun request member => decide_eq_true (clocks request member).2.1
  have fulfilled := nonzero_matching matching
  rw [allCalls] at fulfilled
  refine ⟨fulfilled, ?_, (fulfilled.map Request.time).nodup_iff.mp unique⟩
  intro worker present
  by_cases zero : worker.time = (0, 0)
  · rw [zero]
    norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
  · have admitted : worker ∈ fulfillments.filter (fun request => decide (Live request)) :=
      List.mem_filter.mpr ⟨present, decide_eq_true zero⟩
    have facts := clocks worker (fulfilled.mem_iff.mpr admitted)
    exact ⟨facts.1, facts.2.2⟩

theorem unique_fulfillment {calls : List (Request p)} {workers : List (Delegation.Row p)}
    (matching : calls.Perm ((workers.map fulfillment).filter (fun request => decide (Live request))))
    (unique : (calls.map Request.time).Nodup) {call : Request p} (called : call ∈ calls) :
    ∃! worker, worker ∈ workers ∧ fulfillment worker = call := by
  have admitted := matching.mem_iff.mp called
  have live : Live call := of_decide_eq_true (List.mem_filter.mp admitted).2
  obtain ⟨worker, present, same⟩ := List.mem_map.mp (List.mem_filter.mp admitted).1
  let issued := workers.filter fun worker => decide (Live (fulfillment worker))
  have issuedUnique : (issued.map (fun worker => (fulfillment worker).time)).Nodup := by
    simpa only [List.filter_map, List.map_map, Function.comp_def, issued]
      using (matching.map Request.time).nodup_iff.mp unique
  have chosen : worker ∈ issued := List.mem_filter.mpr ⟨present, by rw [same]; exact decide_eq_true live⟩
  refine ⟨worker, ⟨present, same⟩, ?_⟩
  intro other otherMatch
  have included : other ∈ issued := List.mem_filter.mpr
    ⟨otherMatch.1, by rw [otherMatch.2]; exact decide_eq_true live⟩
  exact List.inj_on_of_nodup_map issuedUnique included chosen
    ((congrArg Request.time otherMatch.2).trans (congrArg Request.time same).symm)

theorem zero_time_fulfillment_invisible (address : Nat) :
    Matching ([] : List (Request p)) [⟨address, (0, 0)⟩] := by
  simp [Matching, Request.issued, Request.empty, Request.token]

end Airbender.Delegation.Requests.Proofs
