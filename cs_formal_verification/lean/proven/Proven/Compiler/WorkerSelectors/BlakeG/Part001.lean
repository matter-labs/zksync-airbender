module
public import Proven.Compiler.WorkerSelectors.BlakeG.Chains
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch001 : List NativeLookups.Selector :=
  ((selectorsFor .blakeG).drop 16).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved001 : batch001.all (fun selector =>
    match NativeLookups.select (circuitFor .blakeG) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .blakeG) batch001).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .blakeG) batch001 = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped001 : batch001.all grouping = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
