module
public import Proven.Compiler.WorkerSelectors.Assemble
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho.Grouped
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho.Part000
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho.Part001
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho.Part002
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho.Part003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
set_option maxRecDepth 32768

/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .thetaRho) =
      .ok ((selectorsFor .thetaRho).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .thetaRho).all (fun selector =>
      match NativeLookups.select (circuitFor .thetaRho) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .thetaRho) (selectorsFor .thetaRho) = true := by
  refine ⟨?_, ?_, ?_⟩
  · unfold NativeLookups.queryLocators NativeLookups.locators
    rw [compiled_gates_toList]
    kernel_rfl
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .thetaRho) selector with
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

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
