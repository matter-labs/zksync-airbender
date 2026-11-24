module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
namespace Airbender.Compiler.NativeWorkerLookups.Proofs
set_option warningAsError true

/-- Each contiguous batch satisfies the same selector predicate. -/
def AllBatches {α : Type} (predicate : α → Bool) : List (List α) → Prop
  | [] => True
  | first :: rest => first.all predicate = true ∧ AllBatches predicate rest

/-- Concatenation retains every checked selector occurrence in order. -/
theorem flatten_all {α : Type} (predicate : α → Bool) (batches : List (List α)) :
    AllBatches predicate batches → batches.flatten.all predicate = true := by
  induction batches with
  | nil => intro _; rfl
  | cons first rest induction =>
    intro accepted
    exact append_all predicate accepted.1 (induction accepted.2)

end Airbender.Compiler.NativeWorkerLookups.Proofs
