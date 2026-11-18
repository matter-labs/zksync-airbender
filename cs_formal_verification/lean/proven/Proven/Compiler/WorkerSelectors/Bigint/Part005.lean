module
public import Proven.Compiler.WorkerSelectors.Bigint.Chains
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch005 : List NativeLookups.Selector :=
  ((selectorsFor .bigint).drop 80).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved005 : batch005.all (fun selector =>
    match NativeLookups.select (circuitFor .bigint) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .bigint) batch005).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .bigint) batch005 = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped005 : batch005.all grouping = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
