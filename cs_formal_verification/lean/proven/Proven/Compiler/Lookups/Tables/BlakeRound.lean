module
public import Human.Compiler.WorkerLookups
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List NativeLookups.Selector := [
  ⟨2, 45, 1, []⟩,
  ⟨0, 90, 1, [178]⟩
]

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : NativeLookups.TableSidesRead (circuitFor .blakeRound) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor .blakeRound) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
