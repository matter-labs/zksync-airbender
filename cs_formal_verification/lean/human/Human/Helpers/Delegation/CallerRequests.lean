import Human.Circuits.AddSub.Artifact
import Human.Helpers.Delegation.Requests

namespace Airbender.Delegation.Requests
open Trace

/-- Caller token from the actual ADD/SUB rs2 port and starting clock.
    This virtual port uses the imported in-cycle offset one. -/
def callerPort : MemoryPort := AddSub.importedConstraintsMemoryPorts[1]

/-- Native selector seven identifies a delegation caller. The descriptor
    comes from the same imported decoder placement used by other instructions. -/
def Selected (w : Nat → ZMod p) : Prop :=
  w AddSub.importedConstraintsDecoderColumns.flags[7] = 1

instance (w : Nat → ZMod p) : Decidable (Selected w) := inferInstanceAs
  (Decidable (w AddSub.importedConstraintsDecoderColumns.flags[7] = 1))

def caller (w : Nat → ZMod p) : Request p :=
  let initial := rawPair w AddSub.importedConstraintsTraceColumns.initialTime
  ⟨(w AddSub.importedConstraintsDecoderColumns.rs2).val,
    (initial.1 + callerPort.clock.offset, initial.2)⟩

end Airbender.Delegation.Requests
