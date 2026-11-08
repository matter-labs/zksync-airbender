module
public import Slop.ShiftBinop.Trace

@[expose] public section

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod p) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

end Airbender.ShiftBinop.Proofs
