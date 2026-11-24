module
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Compiler.NativeSetups.Bigint

@[expose] public section

/- The import claim of the bigint setup. This module reads the raw setup data; the table definitions do not import
   it. -/

namespace Airbender.Bigint

/-- The fixed rows, then zero padding, are the imported native rows on the complete trace domain. -/
def SetupImportClaim : Prop :=
  Compiler.NativeSetups.bigintSetup.traceLen = 4194304 ∧
  Compiler.NativeSetups.bigintSetup.Rows fun index =>
    if bound : index < 1390592 then
      let row := setupRow ⟨index, bound⟩
      #v[(row.1 : Int), (row.2.1 : Int), (row.2.2 : Int)]
    else #v[0, 0, 0]

end Airbender.Bigint
