module
public import Human.Circuits.Keccak.Tables.Controller
public import Human.Compiler.NativeSetups.Keccak

@[expose] public section

/- The import claim of the Keccak setup. This module reads the raw setup data; the table definitions do not import
   it. -/

namespace Airbender.Keccak.Controller
set_option warningAsError true

/-- The fixed regions, the controller rows of `rows`, then zero padding, are the imported native rows on the
    complete trace domain. -/
def SetupImportClaim : Prop :=
  Compiler.NativeSetups.keccakSetup.traceLen = 4194304 ∧
  Compiler.NativeSetups.keccakSetup.Rows fun index =>
    if bound : index < 1249281 then (setupRow rows ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else Vector.replicate 8 0

end Airbender.Keccak.Controller
