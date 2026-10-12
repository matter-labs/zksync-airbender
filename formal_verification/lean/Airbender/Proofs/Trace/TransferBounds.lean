import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Trace.Proofs.Transfer
set_option warningAsError true


def WriteRules (data : Data p) : Prop :=
  ∀ edge ∈ data.steps,
    (∀ previous ∈ data.steps, (timeOfPair previous.2.time).value ≤ (timeOfPair edge.2.time).value →
      previous.1.word.Bounded) → edge.2.word.Bounded

theorem produced_bounds_of_seed {data : Data p} (facts : Facts data)
    (seeds : ∀ token ∈ data.initial, token.word.Bounded)
    (rules : WriteRules data) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.word.Bounded := by
  have result : ∀ time, ∀ token ∈ data.initial ++ data.steps.map Prod.snd,
      (timeOfPair token.time).value = time → token.word.Bounded := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro token member clock
      rcases List.mem_append.mp member with initial | written
      · exact seeds token initial
      · obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp written
        apply rules edge edgeMember
        intro previous present earlier
        have less := lt_of_lt_of_le (facts.order previous present) earlier
        rw [clock] at less
        apply ih _ less previous.1 _ rfl
        exact facts.matching.mem_iff.mpr
          (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨previous, present, rfl⟩)))
  intro token member
  exact result _ token member rfl

theorem produced_bounds {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : Inputs data before cells)
    (rules : WriteRules data) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, token.word.Bounded :=
  produced_bounds_of_seed facts (image_bounds inputs.initialization) rules

theorem read_bounds {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : Inputs data before cells)
    (rules : WriteRules data) : ∀ edge ∈ data.steps, edge.1.word.Bounded := by
  intro edge present
  exact produced_bounds facts inputs rules edge.1 (facts.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, present, rfl⟩))))

theorem terminal_bounds {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : Inputs data before cells)
    (rules : WriteRules data) : ∀ token ∈ data.terminal, token.word.Bounded := by
  intro token present
  exact produced_bounds facts inputs rules token
    (facts.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl present)))

end Airbender.Trace.Proofs.Transfer
