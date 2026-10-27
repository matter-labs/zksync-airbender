import Airbender.Proofs.GKRProtocol.LogicalLookup

namespace Airbender.Compiler
set_option warningAsError true

/-- Re-index a finite list of matching tuples. Natural multiplicities can be
represented by repeated setup indices, so no finite-field counter arithmetic
or nonzero-weight membership premise is needed by callers of `segment`. -/
noncomputable def LookupArgument.ofMembers {ι α : Type} {table : ι → α}
    {requests : List α} (valid : ∀ query ∈ requests, ∃ row, query = table row) :
    LookupArgument table requests := by
  classical
  have indexed : ∃ rows : List ι, rows.map table = requests := by
    induction requests with
    | nil => exact ⟨[], rfl⟩
    | cons query rest proof =>
      obtain ⟨row, same⟩ := valid query List.mem_cons_self
      obtain ⟨rows, restSame⟩ := proof (fun item member => valid item (List.mem_cons_of_mem _ member))
      exact ⟨row :: rows, by simp only [List.map_cons, restSame, ← same]⟩
  let rows := Classical.choose indexed
  have matched : rows.map table = requests := Classical.choose_spec indexed
  have singleton : rows.flatMap (fun row => List.replicate 1 (table row)) = rows.map table := by
    simpa only [List.replicate_one] using
      (List.map_eq_flatMap (f := table) (l := rows)).symm
  exact ⟨rows, fun _ => 1, List.Perm.of_eq (matched.symm.trans singleton.symm)⟩

/-- A trace-wide exact lookup argument supplies each participating row's local
argument. This connects batch matching to the physical row entrypoints without
assuming authored membership separately. -/
noncomputable def LookupArgument.segment {ι α : Type} {table : ι → α}
    {chunks : List (List α)} (argument : LookupArgument table (chunks.flatMap id))
    {chunk : List α} (included : chunk ∈ chunks) : LookupArgument table chunk :=
  LookupArgument.ofMembers fun _ member =>
    argument.member (List.mem_flatMap.mpr ⟨chunk, included, member⟩)

end Airbender.Compiler
