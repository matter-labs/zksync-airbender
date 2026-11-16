module
public import Proven.Compiler.WorkerSelectors.Common
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch001 : List NativeLookups.Selector :=
  ((selectorsFor .columnParity).drop 16).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved001 : batch001.all (fun selector =>
    match NativeLookups.select (circuitFor .columnParity) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .columnParity) batch001).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .columnParity) batch001 = true from by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
