import Human.Helpers.Delegation.Requests
import Human.Helpers.Decoder.Program
import Human.Helpers.Context.FamilyLayout
import Human.Helpers.Delegation.CallerRequests

namespace Airbender.Delegation.Caller
open Trace Arithmetic

/-- Query fields read from the imported ADD/SUB decoder placement. -/
def nativeQuery (w : Nat → ZMod p) : Vector (ZMod p) 9 :=
  nativeDecoderQuery AddSub.importedConstraintsTraceColumns AddSub.importedConstraintsDecoderColumns w

/-- Destination word from the imported native write port. Numeric placements
    stay inside the artifact; reviewers only see the written word. -/
def destination (w : Nat → ZMod p) : Word :=
  (writeToken AddSub.importedConstraintsTraceColumns w
    AddSub.importedConstraintsMemoryPorts[2]).word

/-- The caller's architectural ports are rs1 and rd, both decoded as x0.
    The intervening rs2 port is the full virtual CSR request, not a GPR. -/
def sourceToken (w : Nat → ZMod p) : MemoryToken p :=
  readToken w AddSub.importedConstraintsMemoryPorts[0]

def destinationToken (w : Nat → ZMod p) : MemoryToken p :=
  writeToken AddSub.importedConstraintsTraceColumns w AddSub.importedConstraintsMemoryPorts[2]

/-- PC observations use the imported native state columns. These words are
    mappings of the assignment; their bounds and behavior are proved below. -/
def initialPC (w : Nat → ZMod p) : Word :=
  (⟨.addSub, w⟩ : Trace.Row p).start.word

def finalPC (w : Nat → ZMod p) : Word :=
  (⟨.addSub, w⟩ : Trace.Row p).finish.word

end Airbender.Delegation.Caller
