module
public import Human.Circuits.Blake2G.Tables.Controller
public import Human.Compiler.NativeSetups.BlakeG

@[expose] public section

/- The import claim of the G setup. This module reads the raw setup data; the table definitions do not import it. -/

namespace Airbender.Blake2G.Control

/-- The XOR rows, the controller rows of `controllerRows`, then zero padding, are the imported native rows on the
    complete trace domain. -/
def SetupImportClaim : Prop :=
  Compiler.NativeSetups.blakeGSetup.traceLen = 4194304 ∧
  Compiler.NativeSetups.blakeGSetup.Rows fun index =>
    if bound : index < 344896 then (setupRow controllerRows ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else Vector.replicate 9 0

end Airbender.Blake2G.Control
