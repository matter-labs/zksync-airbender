module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.BlakeG.Grouped
public import Proven.Compiler.WorkerSelectors.BlakeG.Part000
public import Proven.Compiler.WorkerSelectors.BlakeG.Part001
public import Proven.Compiler.WorkerSelectors.BlakeG.Part002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
set_option maxRecDepth 32768

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .blakeG) =
      .ok ((selectorsFor .blakeG).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .blakeG).all (fun selector =>
      match NativeLookups.select (circuitFor .blakeG) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .blakeG) (selectorsFor .blakeG) = true := by
  refine ⟨?_, ?_, ?_⟩
  · unfold NativeLookups.queryLocators NativeLookups.locators
    rw [compiled_gates_toList]
    kernel_rfl
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .blakeG) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate [batch000, batch001, batch002] :=
      by
      refine ⟨?_, ?_, ?_, True.intro⟩
      · kernel_exact resolved000
      · kernel_exact resolved001
      · kernel_exact resolved002
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate [batch000, batch001, batch002] accepted)
  · kernel_exact grouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
