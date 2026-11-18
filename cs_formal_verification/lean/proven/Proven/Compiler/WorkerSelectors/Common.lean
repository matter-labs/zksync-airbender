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

/-- The compiled gates in list form, so that the kernel reads the layers without building the gate array. -/
theorem compiled_gates_toList (circuit : Circuit) : (NativeLookups.compiledGates circuit).toList =
    circuit.layers.toList.flatMap (fun layer => layer.gates.toList ++ layer.gates_with_external_connections.toList) := by
  simp [NativeLookups.compiledGates, Array.toList_flatMap]

/-- With known chains, the group check reads each selector against these chains. -/
theorem groups_agree_of_chains {circuit : Circuit} {groups : List ((Nat × Nat) × Fin 3)}
    (known : NativeLookups.chainGroups circuit = .ok groups) (selectors : List NativeLookups.Selector) :
    NativeLookups.groupsAgree circuit selectors = selectors.all (fun selector =>
      (groups.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]) := by
  unfold NativeLookups.groupsAgree
  rw [known]

end Airbender.Compiler.NativeWorkerLookups.Proofs
