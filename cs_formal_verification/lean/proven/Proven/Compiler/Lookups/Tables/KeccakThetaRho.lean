module
public import Human.Compiler.WorkerLookups
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List NativeLookups.Selector := [
  ⟨2, 19, 1, []⟩,
  ⟨0, 21, 1, [37]⟩
]

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : NativeLookups.TableSidesRead (circuitFor .thetaRho) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor .thetaRho) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
