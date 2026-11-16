module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Grouped
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part000
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part001
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part002
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Part003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
set_option maxRecDepth 32768

/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .columnParity = ([batch000, batch001, batch002, batch003]).flatten := by kernel_rfl

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .columnParity) =
      .ok ((selectorsFor .columnParity).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .columnParity).all (fun selector =>
      match NativeLookups.select (circuitFor .columnParity) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .columnParity) (selectorsFor .columnParity) = true := by
  refine ⟨by kernel_rfl, ?_, ?_⟩
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .columnParity) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate [batch000, batch001, batch002, batch003] :=
      by
      refine ⟨?_, ?_, ?_, ?_, True.intro⟩
      · kernel_exact resolved000
      · kernel_exact resolved001
      · kernel_exact resolved002
      · kernel_exact resolved003
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate [batch000, batch001, batch002, batch003] accepted)
  · kernel_exact grouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
