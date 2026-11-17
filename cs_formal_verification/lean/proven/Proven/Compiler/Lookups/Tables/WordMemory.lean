module
public import Human.Compiler.LookupSelectors
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.WordMemory
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List Selector := [
  ⟨1, 13, 1, []⟩,
  ⟨2, 15, 1, []⟩,
  ⟨0, 20, 1, [15]⟩
]

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : TableSidesRead (circuitFor (.pooled .wordMemory)) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor (.pooled .wordMemory)) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end Airbender.Compiler.NativeLookups.Proofs.WordMemory
