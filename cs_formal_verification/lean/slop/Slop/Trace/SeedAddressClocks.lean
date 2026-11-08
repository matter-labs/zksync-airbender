module
public import Slop.Trace.SeedTransfer

@[expose] public section

/-! State-free twin of `TransferHistory.raw_address_clocks_distinct` for any `Transfer.Data`: from the seed facts
    (`SeedTransfer.SeedInputs`), no (clock, address) pair repeats among the raw events. -/

namespace Airbender.Trace.Proofs.SeedTransfer
set_option warningAsError true

private theorem address_clocks_distinct (events : List MemoryAccess)
    (perAddress : ∀ address, ((events.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup) :
    (events.map fun event => (event.1, event.2.1)).Nodup := by
  induction events with
  | nil => simp
  | cons first rest ih =>
    have tailLocal : ∀ address,
        ((rest.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup := by
      intro address
      have whole := perAddress address
      by_cases same : first.2.1 = address
      · simp only [List.filter_cons, same, decide_true, ite_true, List.map_cons, List.nodup_cons] at whole
        exact whole.2
      · simpa only [List.filter_cons, same, decide_false, Bool.false_eq_true, ite_false] using whole
    refine List.nodup_cons.mpr ⟨?_, ih tailLocal⟩
    intro present
    obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp present
    have here := perAddress first.2.1
    simp only [List.filter_cons, decide_true, ite_true, List.map_cons, List.nodup_cons] at here
    apply here.1
    apply List.mem_map.mpr
    refine ⟨other, List.mem_filter.mpr ⟨otherMember, ?_⟩, ?_⟩
    · simpa using (Prod.ext_iff.mp equal).2
    · exact (Prod.ext_iff.mp equal).1

theorem raw_address_clocks_distinct {data : Transfer.Data p} (facts : Transfer.Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
    ((Transfer.rawEvents data).map fun event => (event.1, event.2.1)).Nodup := by
  apply address_clocks_distinct
  intro address
  obtain ⟨history, permutation, _⟩ := raw_cell_history facts inputs address
  have unique : (history.val.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact history.property.imp (by
      intro a b less equal
      change b.1 < a.1 at less
      omega)
  exact (permutation.map Prod.fst).nodup_iff.mp unique

end Airbender.Trace.Proofs.SeedTransfer
