module
public import Proven.Compiler.WorkerSelectors.Bigint.Chains
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch006 : List NativeLookups.Selector :=
  ((selectorsFor .bigint).drop 96).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved006 : batch006.all (fun selector =>
    match NativeLookups.select (circuitFor .bigint) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .bigint) batch006).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .bigint) batch006 = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped006 : batch006.all grouping = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.Bigint
