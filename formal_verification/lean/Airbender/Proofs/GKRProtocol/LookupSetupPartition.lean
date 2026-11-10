import Airbender.Review.Compiler.LookupArgument

namespace Airbender.Compiler.LookupArgument
set_option warningAsError true
set_option Elab.async false
variable {ι α : Type}

private def selectedRows (table : ι → α) (keep : α → Bool) (rows : List ι) :
    List {index : ι // keep (table index) = true} :=
  rows.filterMap fun index =>
    if checked : keep (table index) = true then some ⟨index, checked⟩ else none

private theorem selected_rows_balance (table : ι → α) (keep : α → Bool)
    (multiplicity : ι → Nat) (rows : List ι) :
    (rows.flatMap fun index => List.replicate (multiplicity index) (table index)).filter keep =
      (selectedRows table keep rows).flatMap fun index =>
        List.replicate (multiplicity index.val) (table index.val) := by
  induction rows with
  | nil => rfl
  | cons index rest ih =>
    cases checked : keep (table index) <;>
      simp [selectedRows, checked, ih]

/-- Select both sides of exact matching with the same tuple predicate.
The original natural multiplicity remains attached to each retained row. -/
def restrictTo {table : ι → α} {requests : List α}
    (argument : LookupArgument table requests) (keep : α → Bool) :
    LookupArgument (fun index : {index : ι // keep (table index) = true} => table index.val)
      (requests.filter keep) where
  rows := selectedRows table keep argument.rows
  multiplicity index := argument.multiplicity index.val
  balance := by
    have matching := argument.balance.filter keep
    rw [selected_rows_balance] at matching
    exact matching

/-- Derive the two exact arguments for a setup partition. No new matching
premise is needed. A native binding must still identify the tuple predicate. -/
def splitBy {table : ι → α} {requests : List α}
    (argument : LookupArgument table requests) (isProgram : α → Bool) :
    LookupArgument
        (fun index : {index : ι // (!isProgram (table index)) = true} => table index.val)
        (requests.filter fun tuple => !isProgram tuple) ×
      LookupArgument
        (fun index : {index : ι // isProgram (table index) = true} => table index.val)
        (requests.filter isProgram) :=
  ⟨argument.restrictTo (fun tuple => !isProgram tuple), argument.restrictTo isProgram⟩

end Airbender.Compiler.LookupArgument
