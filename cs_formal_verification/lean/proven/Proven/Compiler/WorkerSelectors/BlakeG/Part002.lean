module
public import Proven.Compiler.WorkerSelectors.Common
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch002 : List NativeLookups.Selector :=
  ((selectorsFor .blakeG).drop 32).take 8

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved002 : batch002.all (fun selector =>
    match NativeLookups.select (circuitFor .blakeG) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .blakeG) batch002).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .blakeG) batch002 = true from by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
