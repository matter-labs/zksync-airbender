module
public import Proven.Compiler.WorkerSelectors.Bigint
public import Proven.KernelRfl
public import Proven.Compiler.WorkerSelectors.BlakeG
public import Proven.Compiler.WorkerSelectors.BlakeRound
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho
public import Proven.Compiler.WorkerSelectors.KeccakChi5
public import Proven.Compiler.Lookups.Tables

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups
set_option maxRecDepth 32768

/-- Every cached worker selector has its actual native operand and chain group. -/
theorem cached_worker_lookup_selectors : CachedWorkerLookupSelectorsClaim := by
  intro family
  have tables := Proofs.tables family
  have binding : NativeLookups.queryLocators (circuitFor family) =
      .ok ((selectorsFor family).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor family).all (fun selector =>
      match NativeLookups.select (circuitFor family) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor family) (selectorsFor family) = true := by
    cases family with
    | bigint => kernel_exact Proofs.Bigint.binding
    | blakeG => kernel_exact Proofs.BlakeG.binding
    | blakeRound => kernel_exact Proofs.BlakeRound.binding
    | columnParity => kernel_exact Proofs.KeccakColumnParity.binding
    | thetaRho => kernel_exact Proofs.KeccakThetaRho.binding
    | chi5 => kernel_exact Proofs.KeccakChi5.binding
  obtain ⟨covered, resolved, grouped⟩ := binding
  exact ⟨covered, resolved, grouped, tables⟩

/-- A nonempty bigint query list supplies all selector premises. -/
theorem cached_worker_lookup_selectors_satisfiable : CachedWorkerLookupSelectorsSatisfiableClaim := by
  have nonempty : selectorsFor .bigint ≠ [] := by
    intro empty
    have size : (selectorsFor .bigint).length = 134 := by kernel_rfl
    rw [empty] at size
    contradiction
  refine ⟨.bigint, nonempty, ?_⟩
  obtain ⟨covered, resolved, grouped⟩ := Proofs.Bigint.binding
  kernel_exact And.intro covered (And.intro resolved (And.intro grouped Proofs.Bigint.tables))

end Airbender.Compiler.NativeWorkerLookups
