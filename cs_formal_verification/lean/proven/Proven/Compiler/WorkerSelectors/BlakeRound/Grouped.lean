module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .blakeRound) (selectorsFor .blakeRound) = true := by kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
