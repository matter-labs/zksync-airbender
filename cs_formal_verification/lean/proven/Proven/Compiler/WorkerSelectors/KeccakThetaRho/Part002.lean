module
public import Proven.Compiler.WorkerSelectors.KeccakThetaRho.Chains
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
set_option maxRecDepth 32768

/-- This contiguous batch retains the native query order. -/
def batch002 : List NativeLookups.Selector :=
  ((selectorsFor .thetaRho).drop 32).take 16

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved002 : batch002.all (fun selector =>
    match NativeLookups.select (circuitFor .thetaRho) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .thetaRho) batch002).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .thetaRho) batch002 = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped002 : batch002.all grouping = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
