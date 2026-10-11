import Airbender.Review.Delegation.Requests
import Airbender.Review.Trace.Program

namespace Airbender.Delegation.Caller
open Trace Arithmetic

/-- Admit the four pinned project's delegation CSRRW forms. Sail supplies the
    actual decoded instruction; this projection supplies native circuit metadata.
    Both architectural operands are x0. The virtual CSR address is retained
    separately in `query`, not treated as a five-bit GPR index. -/
def decoderFields : SailRV32.instruction → Option (DecoderData Family)
  | .CSRReg (address, .Regidx source, .Regidx destination, .CSRRW) =>
    if source = 0 ∧ destination = 0 then
      if address = 0x7CA then some ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
      else if address = 0x7C8 then some ⟨.blakeG, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
      else if address = 0x7C7 then some ⟨.blakeRound, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
      else if address = 0x7CB then some ⟨.keccak, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
      else none
    else none
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Family

/-- Construct caller entries by reading public bytes and running pinned Sail
    decoding. Unreadable, invalid or unsupported instructions are rejected. -/
abbrev programImage := Trace.programImageRunWith decoderFields

/-- The actual ADD/SUB decoder query for a delegation caller. Its rs2 field
    is the full virtual CSR address. Other register/immediate fields are zero;
    bit seven selects delegation. Source: `add_sub_family/decoder.rs`. -/
def query {p : Nat} (entry : ProgramEntry) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, 0, Requests.csr entry.data.family, 0, 0, 0, 0, 128]

/-- The current modeled caller table, constructed from public Sail entries.
    Membership binds native fields to one actual instruction entry. This is
    logical table membership; setup extraction and cryptographic enforcement
    remain outside the claim. -/
def decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.DelegationCaller"
  length := program.length
  row i := query (program.get i)
  index values := program.toArray.findIdx (fun entry => query entry == values)
  Spec values := ∃ entry ∈ program, values = query entry
  contains_iff := by
    intro values
    constructor
    · rintro ⟨i, equal⟩
      exact ⟨program.get i, List.get_mem _ _, equal⟩
    · rintro ⟨entry, member, equal⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      exact ⟨i, equal⟩ }

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

/-- Caller PC effects, tied to actual public decoding. Range queries prove
    the final word is canonical. Sail's original preparation and retirement
    accessors produce the same PC; delegated memory effects are separate. -/
structure PCBinding (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State)
    (program : List ProgramEntry) : Prop where
  /-- The native starting PC locates one actual public caller instruction. -/
  instruction : ∃ entry ∈ program, entry.SourceWith before decoderFields ∧
    initialPC w = Word.ofBitVec entry.pc
  /-- Both final PC limbs are ranged by the imported lookup queries. -/
  bounded : (finalPC w).Bounded
  /-- The retained PC equations advance the decoded address by four. -/
  advances : (finalPC w).toBitVec = (initialPC w).toBitVec + 4
  /-- This is the original Sail PC path, in any state with that readable PC. -/
  sail : ∀ state : Reference.RiscV.Sail.State,
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) state =
      .ok (initialPC w).toBitVec state →
    Reference.Sail.run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) state =
      .ok () { state with regs :=
        (state.regs.insert .nextPC (finalPC w).toBitVec).insert .PC (finalPC w).toBitVec }

/-- What an accepted caller proves: one actual public Sail instruction,
    its full CSR request token, and a zero architectural destination word.
    These are conclusions; no selected instruction or desired result is assumed. -/
structure Binding (w : Nat → ZMod p) (before : Reference.RiscV.Sail.State)
    (program : List ProgramEntry) : Prop where
  /-- Successful public decoding determines the invoked family. -/
  instruction : ∃ entry ∈ program, entry.SourceWith before decoderFields ∧
    (Requests.caller w).csr = Requests.csr entry.data.family
  /-- The virtual CSR read consumes the empty token. -/
  emptyRead : readToken w Requests.callerPort = (Requests.caller w).empty
  /-- The virtual CSR write issues this row's invocation clock. -/
  issuedWrite : writeToken AddSub.importedConstraintsTraceColumns w Requests.callerPort =
    (Requests.caller w).issued
  /-- The imported destination write contains zero. -/
  zeroDestination : destination w = ⟨0, 0⟩
  /-- The real source port addresses x0. Its native read value is established
      by initialized architectural history, not by this local request claim. -/
  sourceAddress : (sourceToken w).address = (Cell.register 0).addressCode
  /-- The real destination port addresses x0; the virtual CSR stays separate. -/
  destinationAddress : (destinationToken w).address = (Cell.register 0).addressCode
  /-- Original Sail reads x0 as zero and discards the native zero write.
      These operations preserve the entire state, including memory and CSRs. -/
  registerEffects : ∀ state : Reference.RiscV.Sail.State,
    (Cell.register 0).read state = .ok 0 state ∧
    Reference.Sail.run ((Cell.register 0).write (destination w).toBitVec) state = .ok () state

end Airbender.Delegation.Caller
