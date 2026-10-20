import Human.Circuits.Blake2G.Controller

namespace Airbender.Blake2G.Control

def Output.row (output : Output) : Vector Nat 7 :=
  #v[output.register.lo, output.stateOffsets[0], output.stateOffsets[1],
    output.stateOffsets[2], output.stateOffsets[3], output.messageOffsets[0], output.messageOffsets[1]]

def controllerRows (key : Fin 512) : Vector Nat 7 :=
  (step ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ key.val)⟩).row

end Airbender.Blake2G.Control
