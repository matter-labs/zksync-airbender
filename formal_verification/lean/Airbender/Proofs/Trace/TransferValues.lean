import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Trace.Proofs.Transfer
set_option warningAsError true

theorem produced_cell_values {data : Data p} (facts : Facts data) (address value : Nat)
    (initial : ∀ token ∈ data.initial, token.address = address → token.value = value)
    (closed : ∀ edge ∈ data.steps, edge.1.address = address →
      edge.1.value = value → edge.2.value = value) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.address = address → token.value = value := by
  have result : ∀ time, ∀ token ∈ data.initial ++ data.steps.map Prod.snd,
      (timeOfPair token.time).value = time → token.address = address → token.value = value := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro token member clock same
      rcases List.mem_append.mp member with seed | written
      · exact initial token seed same
      · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
        have key := (facts.addresses edge present).trans same
        apply closed edge present key
        apply ih _ (by simpa only [clock] using facts.order edge present) edge.1
          (facts.matching.mem_iff.mpr
            (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩)))) rfl key
  intro token member same
  exact result _ token member rfl same

theorem read_cell_values {data : Data p} (facts : Facts data) (address value : Nat)
    (initial : ∀ token ∈ data.initial, token.address = address → token.value = value)
    (closed : ∀ edge ∈ data.steps, edge.1.address = address →
      edge.1.value = value → edge.2.value = value) :
    ∀ edge ∈ data.steps, edge.1.address = address → edge.1.value = value := by
  intro edge member same
  exact produced_cell_values facts address value initial closed edge.1
    (facts.matching.mem_iff.mpr
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))) same

end Airbender.Trace.Proofs.Transfer
