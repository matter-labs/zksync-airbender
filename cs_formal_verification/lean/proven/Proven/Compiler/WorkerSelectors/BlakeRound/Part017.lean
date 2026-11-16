module
public import Proven.Compiler.WorkerSelectors.Common
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch017 : List NativeLookups.Selector :=
  ((selectorsFor .blakeRound).drop 272).take 9

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved017 : batch017.all (fun selector =>
    match NativeLookups.select (circuitFor .blakeRound) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .blakeRound) batch017).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .blakeRound) batch017 = true from by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
