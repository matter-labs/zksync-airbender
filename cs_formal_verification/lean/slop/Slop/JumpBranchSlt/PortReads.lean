import Slop.JumpBranchSlt.Trace

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace

abbrev nativeEvents (epoch : Nat) (w : Nat → ZMod p) :=
  Trace.nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w

end Airbender.JumpBranchSlt.Proofs
