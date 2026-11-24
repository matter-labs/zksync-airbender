module
public import Proven.Compiler.WorkerSelectors.KeccakColumnParity.Chains
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch000 : List NativeLookups.Selector :=
  ((selectorsFor .columnParity).drop 0).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved000 : batch000.all (fun selector =>
    match NativeLookups.select (circuitFor .columnParity) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .columnParity) batch000).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .columnParity) batch000 = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped000 : batch000.all grouping = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
