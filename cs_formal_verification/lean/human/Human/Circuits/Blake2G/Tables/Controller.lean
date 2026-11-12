module
public import Human.Circuits.Blake2G.Controller
public meta import Human.Circuits.Blake2G.Controller

public import Human.Import.NativeGrid
public import Human.Compiler.NativeSetups.BlakeG
public meta import Human.Compiler.NativeSetups.BlakeG

public meta import Human.Circuits.Blake2G.Tables.Setup

@[expose] public section

namespace Airbender.Blake2G.Control

def Output.row (output : Output) : Vector Nat 7 :=
  #v[output.register.lo, output.stateOffsets[0], output.stateOffsets[1],
    output.stateOffsets[2], output.stateOffsets[3], output.messageOffsets[0], output.messageOffsets[1]]

def controllerRows (key : Fin 512) : Vector Nat 7 :=
  (step ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ key.val)⟩).row

/- Bind this row formula to every native row. The comparison runs as trusted compiled code. -/
check_native_grid "artifacts/setup/blake-g.json" [344384, 512] ([1, 2, 3, 4, 5, 6, 7]) => (controllerRows)

/- Compare every fixed row with the native export in trusted compiled code. -/
check_native_grid "artifacts/setup/blake-g.json" [0, 344896] ([0,1,2,3,4,5,6,7,8]) => (Airbender.Blake2G.setupRow controllerRows)

end Airbender.Blake2G.Control
