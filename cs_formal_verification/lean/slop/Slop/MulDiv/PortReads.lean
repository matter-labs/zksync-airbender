module
public import Slop.MulDiv.Trace

@[expose] public section

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod p) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

end Airbender.MulDiv.Proofs
