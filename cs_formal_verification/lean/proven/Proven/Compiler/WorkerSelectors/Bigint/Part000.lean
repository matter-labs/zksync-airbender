module
public import Proven.Compiler.WorkerSelectors.Common
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch000 : List NativeLookups.Selector :=
  ((selectorsFor .bigint).drop 0).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved000 : batch000.all (fun selector =>
    match NativeLookups.select (circuitFor .bigint) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .bigint) batch000).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .bigint) batch000 = true from by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
