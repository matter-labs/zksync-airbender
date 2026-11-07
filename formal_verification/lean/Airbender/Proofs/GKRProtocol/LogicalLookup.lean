import Airbender.Review.Compiler.LookupOperands
import Airbender.Review.Compiler.LookupArgument
import Airbender.Proofs.GKRProtocol.GroupedTrace

namespace Airbender.Compiler
set_option warningAsError true

theorem LookupArgument.member {ι α : Type} {table : ι → α} {requests : List α}
    (argument : LookupArgument table requests) {query : α} (member : query ∈ requests) :
    ∃ row, query = table row := by
  have supplied := argument.balance.mem_iff.mp member
  obtain ⟨row, _, repeated⟩ := List.mem_flatMap.mp supplied
  exact ⟨row, (List.mem_replicate.mp repeated).2⟩

theorem activeLookupFields.member {queries : List MaterializedQuery} {query : MaterializedQuery}
    (member : query ∈ queries) (enabled : query.weight ≠ 0) :
    query.fields ∈ activeLookupFields queries := by
  exact List.mem_map.mpr ⟨query, List.mem_filter.mpr ⟨member, by simpa using enabled⟩, rfl⟩


end Airbender.Compiler
