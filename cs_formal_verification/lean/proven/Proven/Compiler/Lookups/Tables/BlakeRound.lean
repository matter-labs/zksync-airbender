module
public import Proven.Compiler.Lookups.Tables.BlakeRound.Grouped
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : NativeLookups.TableSidesRead (circuitFor .blakeRound) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor .blakeRound) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) tablesGrouped

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
