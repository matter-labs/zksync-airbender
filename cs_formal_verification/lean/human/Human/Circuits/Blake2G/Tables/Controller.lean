module
public import Human.Circuits.Blake2G.Controller
public import Human.Circuits.Blake2G.Tables.Setup
public import Human.Compiler.NativeSetups.BlakeG

@[expose] public section

namespace Airbender.Blake2G.Control

def Output.row (output : Output) : Vector Nat 7 :=
  #v[output.register.lo, output.stateOffsets[0], output.stateOffsets[1],
    output.stateOffsets[2], output.stateOffsets[3], output.messageOffsets[0], output.messageOffsets[1]]

def controllerRows (key : Fin 512) : Vector Nat 7 :=
  (step ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ key.val)⟩).row

/-- The XOR rows, the controller rows of `controllerRows`, then zero padding, are the imported native rows on the
    complete trace domain. -/
def SetupImportClaim : Prop :=
  Compiler.NativeSetups.blakeGSetup.traceLen = 4194304 ∧
  Compiler.NativeSetups.blakeGSetup.Rows fun index =>
    if bound : index < 344896 then (setupRow controllerRows ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else Vector.replicate 9 0

end Airbender.Blake2G.Control
