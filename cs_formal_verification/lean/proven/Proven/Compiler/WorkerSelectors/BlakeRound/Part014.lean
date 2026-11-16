module
public import Proven.Compiler.WorkerSelectors.Common
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch014 : List NativeLookups.Selector :=
  ((selectorsFor .blakeRound).drop 224).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved014 : batch014.all (fun selector =>
    match NativeLookups.select (circuitFor .blakeRound) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .blakeRound) batch014).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .blakeRound) batch014 = true from by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
