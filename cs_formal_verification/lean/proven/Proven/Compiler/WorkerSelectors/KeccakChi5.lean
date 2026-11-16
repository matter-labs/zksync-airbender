module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.KeccakChi5.Grouped
public import Proven.Compiler.WorkerSelectors.KeccakChi5.Part000
public import Proven.Compiler.WorkerSelectors.KeccakChi5.Part001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .chi5 = ([batch000, batch001]).flatten := by kernel_rfl

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .chi5) =
      .ok ((selectorsFor .chi5).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .chi5).all (fun selector =>
      match NativeLookups.select (circuitFor .chi5) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .chi5) (selectorsFor .chi5) = true := by
  refine ⟨by kernel_rfl, ?_, ?_⟩
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .chi5) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate [batch000, batch001] :=
      by
      refine ⟨?_, ?_, True.intro⟩
      · kernel_exact resolved000
      · kernel_exact resolved001
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate [batch000, batch001] accepted)
  · kernel_exact grouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
