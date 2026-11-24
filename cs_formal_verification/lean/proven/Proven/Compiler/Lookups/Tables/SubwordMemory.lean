module
public import Human.Compiler.LookupSelectors
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.SubwordMemory
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List Selector := [
  ⟨1, 23, 1, []⟩,
  ⟨2, 25, 1, []⟩,
  ⟨0, 30, 1, [15]⟩
]

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : TableSidesRead (circuitFor (.pooled .subwordMemory)) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor (.pooled .subwordMemory)) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end Airbender.Compiler.NativeLookups.Proofs.SubwordMemory
