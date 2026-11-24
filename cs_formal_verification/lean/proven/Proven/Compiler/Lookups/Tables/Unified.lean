module
public import Human.Compiler.LookupSelectors
public import Proven.Compiler.Lookups.Tables.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.Unified
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List Selector := [
  ⟨1, 48, 1, []⟩,
  ⟨2, 55, 1, []⟩,
  ⟨0, 60, 1, [15]⟩
]

/-- Each lookup group of the cached capture reads its declared multiplicity and setup columns. -/
theorem tables : TableSidesRead (circuitFor (.unified)) :=
  NativeLookups.Proofs.Tables.tableSidesRead_of (circuitFor (.unified)) tableSelectors
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end Airbender.Compiler.NativeLookups.Proofs.Unified
