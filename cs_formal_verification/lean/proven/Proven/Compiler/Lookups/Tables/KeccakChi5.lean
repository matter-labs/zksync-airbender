module
public import Human.Compiler.WorkerLookups
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List NativeLookups.Selector := [
  ⟨2, 15, 1, []⟩,
  ⟨0, 17, 1, [29]⟩
]

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : NativeLookups.TableSidesRead (circuitFor .chi5) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor .chi5) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
