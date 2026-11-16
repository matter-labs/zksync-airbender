module
public import Proven.Compiler.WorkerSelectors.Bigint
public import Proven.KernelRfl
public import Proven.Compiler.WorkerSelectors.BlakeG
public import Proven.Compiler.WorkerSelectors.BlakeRound
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho
public import Proven.Compiler.WorkerSelectors.KeccakChi5

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups
set_option maxRecDepth 32768

/-- Every cached worker selector has its actual native operand and chain group. -/
theorem cached_worker_lookup_selectors : CachedWorkerLookupSelectorsClaim := by
  intro family
  cases family with
  | bigint => kernel_exact Proofs.Bigint.binding
  | blakeG => kernel_exact Proofs.BlakeG.binding
  | blakeRound => kernel_exact Proofs.BlakeRound.binding
  | columnParity => kernel_exact Proofs.KeccakColumnParity.binding
  | thetaRho => kernel_exact Proofs.KeccakThetaRho.binding
  | chi5 => kernel_exact Proofs.KeccakChi5.binding

/-- A nonempty bigint query list supplies all selector premises. -/
theorem cached_worker_lookup_selectors_satisfiable : CachedWorkerLookupSelectorsSatisfiableClaim := by
  have nonempty : selectorsFor .bigint ≠ [] := by
    intro empty
    have size : (selectorsFor .bigint).length = 134 := by kernel_rfl
    rw [empty] at size
    contradiction
  refine ⟨.bigint, nonempty, ?_⟩
  kernel_exact Proofs.Bigint.binding

end Airbender.Compiler.NativeWorkerLookups
