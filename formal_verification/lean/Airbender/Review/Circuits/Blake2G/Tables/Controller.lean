import Airbender.Review.Circuits.Blake2G.Controller

namespace Airbender.Blake2G.Control

def Output.row (output : Output) : Vector Nat 7 :=
  #v[output.register.lo, output.stateOffsets[0], output.stateOffsets[1],
    output.stateOffsets[2], output.stateOffsets[3], output.messageOffsets[0], output.messageOffsets[1]]

def controllerRows (key : Fin 512) : Vector Nat 7 :=
  Vector.ofFn fun j => ((controllerData.columns[j.val + 1]).get? key.val).getD 0

end Airbender.Blake2G.Control
