module
public import Human.Circuits.UnifiedReduced.Decoder
public import Human.Helpers.Delegation.Decoder
public import Human.Helpers.Delegation.CallerRequests

@[expose] public section

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic

/-- The virtual request uses the unified starting clock and in-cycle tick one.
    Its full CSR column and starting clock coincide with the ADD/SUB placement. -/
abbrev request {p : Nat} := Delegation.Requests.caller (p := p)

/-- The rs2 slot is the virtual CSR port. The other two native ports address x0.
    Source: `unified_reduced_machine/add_sub_lui_auipc_mop.rs` and the imported layout. -/
def virtualPort : MemoryPort := importedConstraintsMemoryPorts[1]
def sourceToken (w : Nat → ZMod p) := readToken w importedConstraintsMemoryPorts[0]
def destinationToken (w : Nat → ZMod p) :=
  writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]
def initialPC (w : Nat → ZMod p) : Word :=
  (⟨.machine, w⟩ : Trace.Row p UnifiedFamily).start.word
def finalPC (w : Nat → ZMod p) : Word :=
  (⟨.machine, w⟩ : Trace.Row p UnifiedFamily).finish.word

end Airbender.UnifiedReduced.Caller
