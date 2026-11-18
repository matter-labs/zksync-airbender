module
public import Proven.Compiler.WorkerSelectors.BlakeRound.Chains
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch009 : List NativeLookups.Selector :=
  ((selectorsFor .blakeRound).drop 144).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved009 : batch009.all (fun selector =>
    match NativeLookups.select (circuitFor .blakeRound) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .blakeRound) batch009).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .blakeRound) batch009 = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped009 : batch009.all grouping = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
