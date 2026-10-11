import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.Delegation.Decoder

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic

/-- Reuse the four project caller forms, public byte importer and original Sail
    CSR decoder. The unified circuit uses the same nine-field caller query;
    its selectors and native ports have different imported placements. -/
abbrev ProgramEntry := Delegation.Caller.ProgramEntry
abbrev programImage := Delegation.Caller.programImage
abbrev decoderTable {p : Nat} [Fact p.Prime] := Delegation.Caller.decoderTable (p := p)

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

/-- What public decoding and the unified imported equations prove about a caller.
    No selector, desired request, read value, operand range or PC result is assumed.
    Request matching and initialized worker memory are the next connection. -/
structure Binding (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State)
    (program : List ProgramEntry) : Prop where
  /-- An actual public CSR instruction determines the full-width worker family. -/
  instruction : ∃ entry ∈ program, entry.SourceWith before Delegation.Caller.decoderFields ∧
    (request w).csr = Delegation.Requests.csr entry.data.family
  /-- The imported unified selector marks an active caller. -/
  selected : w importedConstraintsTraceColumns.execute = 1 ∧
    w importedConstraintsDecoderColumns.flags[7] = 1
  /-- The real virtual port consumes the empty token and issues its invocation. -/
  virtual : readToken w virtualPort = (request w).empty ∧
    writeToken importedConstraintsTraceColumns w virtualPort = (request w).issued
  /-- Both architectural ports address x0, and the destination write is zero.
      The source value still comes from initialized architectural history. -/
  registers : (sourceToken w).address = (Cell.register 0).addressCode ∧
    (destinationToken w).address = (Cell.register 0).addressCode ∧
    (destinationToken w).word = ⟨0, 0⟩
  /-- Public decoding binds the starting PC; native queries bound the final PC
      and the retained equations enforce the four-byte successor. -/
  pc : (initialPC w).Bounded ∧ (finalPC w).Bounded ∧
    (finalPC w).toBitVec = (initialPC w).toBitVec + 4
  /-- Original Sail x0 accesses preserve state. Original PC preparation and
      retirement reach the imported final PC. Delegated worker effects remain separate. -/
  sail : ∀ state : Reference.RiscV.Sail.State,
    (Cell.register 0).read state = .ok 0 state ∧
    Reference.Sail.run ((Cell.register 0).write (destinationToken w).word.toBitVec) state = .ok () state ∧
    (Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) state = .ok (initialPC w).toBitVec state →
      Reference.Sail.run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) state =
        .ok () { state with regs :=
          (state.regs.insert .nextPC (finalPC w).toBitVec).insert .PC (finalPC w).toBitVec })

end Airbender.UnifiedReduced.Caller
