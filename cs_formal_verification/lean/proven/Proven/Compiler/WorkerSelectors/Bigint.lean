module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.Bigint.Grouped
public import Proven.Compiler.WorkerSelectors.Bigint.Part000
public import Proven.Compiler.WorkerSelectors.Bigint.Part001
public import Proven.Compiler.WorkerSelectors.Bigint.Part002
public import Proven.Compiler.WorkerSelectors.Bigint.Part003
public import Proven.Compiler.WorkerSelectors.Bigint.Part004
public import Proven.Compiler.WorkerSelectors.Bigint.Part005
public import Proven.Compiler.WorkerSelectors.Bigint.Part006
public import Proven.Compiler.WorkerSelectors.Bigint.Part007
public import Proven.Compiler.WorkerSelectors.Bigint.Part008

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
set_option maxRecDepth 32768

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .bigint) =
      .ok ((selectorsFor .bigint).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .bigint).all (fun selector =>
      match NativeLookups.select (circuitFor .bigint) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .bigint) (selectorsFor .bigint) = true := by
  refine ⟨?_, ?_, ?_⟩
  · unfold NativeLookups.queryLocators NativeLookups.locators
    rw [compiled_gates_toList]
    kernel_rfl
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .bigint) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008] :=
      by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
      · kernel_exact resolved000
      · kernel_exact resolved001
      · kernel_exact resolved002
      · kernel_exact resolved003
      · kernel_exact resolved004
      · kernel_exact resolved005
      · kernel_exact resolved006
      · kernel_exact resolved007
      · kernel_exact resolved008
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate [batch000, batch001, batch002, batch003, batch004, batch005, batch006, batch007, batch008] accepted)
  · kernel_exact grouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
