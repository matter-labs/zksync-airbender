module
public import Human.Compiler.LookupArgument
public import Proven.GKRProtocol.LookupOperands

@[expose] public section
namespace Airbender.Compiler
set_option warningAsError true

/-- Exact tuple matching supplies a setup row for each emitted tuple. -/
theorem LookupArgument.member {ι α : Type} {table : ι → α} {requests : List α}
    (argument : LookupArgument table requests) {query : α} (member : query ∈ requests) :
    ∃ row, query = table row := by
  have supplied := argument.balance.mem_iff.mp member
  obtain ⟨row, _, repeated⟩ := List.mem_flatMap.mp supplied
  exact ⟨row, (List.mem_replicate.mp repeated).2⟩

/-- Every enabled query contributes its complete tuple. -/
theorem activeLookupFields.member {queries : List MaterializedQuery} {query : MaterializedQuery}
    (member : query ∈ queries) (enabled : query.weight ≠ 0) :
    query.fields ∈ activeLookupFields queries := by
  exact List.mem_map.mpr ⟨query, List.mem_filter.mpr ⟨member, by simpa using enabled⟩, rfl⟩

/-- Natural multiplicities and selected row indices survive a request permutation. -/
def LookupArgument.reorder {ι α : Type} {table : ι → α} {first second : List α}
    (argument : LookupArgument table first) (order : first.Perm second) : LookupArgument table second :=
  ⟨argument.rows, argument.multiplicity, order.symm.trans argument.balance⟩

end Airbender.Compiler
