module
public import Slop.SubwordMemory.Values

@[expose] public section

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod p) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

end Airbender.SubwordMemory.Proofs
