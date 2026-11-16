module
public import Human.Compiler.WorkerLookups
public import Proven.Compiler.ChainAddress
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.NativeWorkerLookups.Proofs
set_option warningAsError true

/-- The shared-array check is the same selector-resolution predicate. -/
theorem resolved_all_eq (circuit : Circuit) (selectors : List NativeLookups.Selector) :
    NativeLookups.resolvedAll circuit selectors = selectors.all (fun selector =>
      match NativeLookups.select circuit selector with | .ok _ => true | .error _ => false) := rfl

/-- Independent selector batches preserve the complete list order. -/
theorem append_all {α : Type} (predicate : α → Bool) {first rest : List α}
    (left : first.all predicate = true) (right : rest.all predicate = true) :
    (first ++ rest).all predicate = true := by
  simp only [List.all_append, left, right, Bool.true_and]

/-- Native chain groups agree on a concatenation when they agree on both parts. -/
theorem append_groups (circuit : Circuit) {first rest : List NativeLookups.Selector}
    (left : NativeLookups.groupsAgree circuit first = true)
    (right : NativeLookups.groupsAgree circuit rest = true) :
    NativeLookups.groupsAgree circuit (first ++ rest) = true := by
  cases actual : NativeLookups.chainGroups circuit <;>
    simp_all [NativeLookups.groupsAgree, List.all_append]

end Airbender.Compiler.NativeWorkerLookups.Proofs
