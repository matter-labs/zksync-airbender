import Airbender.Review.Helpers.Context.ExternalBoundary.Requests
import Airbender.Proofs.UnifiedReduced.RequestTrace
import Airbender.Proofs.ExternalBoundary.NativeRequests

namespace Airbender.ExternalBoundary.Requests.Proofs
open Trace Arithmetic UnifiedReduced.Caller
set_option warningAsError true

theorem covered [Fact p.Prime] {data : RequestTrace p}
    {before : Reference.RiscV.Sail.State} (native : RequestBinding data before)
    (external : Binding data) : Covered data := by
  intro worker member
  have fulfilled : Delegation.Requests.fulfillment worker ∈ data.fulfillments :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  obtain ⟨caller, present, equal⟩ := List.mem_map.mp (external.mem_iff.mpr fulfilled)
  obtain ⟨selected, ⟨selectedMember, matched, slot⟩, _⟩ := native.workers caller present
  obtain ⟨chosen, _, only⟩ := Delegation.Requests.Proofs.unique_fulfillment
    native.fulfilled native.invocations.1 (List.mem_map.mpr ⟨caller, present, rfl⟩)
  have same : worker = selected :=
    (only worker ⟨member, equal.symm⟩).trans (only selected ⟨selectedMember, matched⟩).symm
  subst worker
  exact ⟨caller, present, matched, slot⟩

theorem no_zero [Fact p.Prime] {data : RequestTrace p}
    {before : Reference.RiscV.Sail.State} (native : RequestBinding data before)
    (external : Binding data) :
    ∀ worker ∈ data.workers.rows, (Delegation.Requests.fulfillment worker).time ≠ (0, 0) := by
  intro worker member zero
  obtain ⟨caller, present, matched, _⟩ := covered native external worker member
  exact ((native.unissued worker member).mpr zero) ⟨caller, present, matched⟩

end Airbender.ExternalBoundary.Requests.Proofs
