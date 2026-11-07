import Human.Helpers.Delegation.Decoder
import Human.Helpers.Decoder.RVProgram
import Human.Helpers.Context.RVRowContext

/-! RV siblings of the delegation caller decoder (`Decoder.lean`): the public caller table is built from an `RV.State`
    (`rvProgramImageWith`: the ROM image's bytes, `RV.decode`, then `rvDecoderFields`); an admitted entry decodes to
    `.delegate k` (`csrrw x0, <csr>, x0`) for one of the four caller families. No `Configured`. The native row columns
    (`nativeQuery`, `destination`, the ports and PC words) are the Sail-free definitions of `Decoder.lean`. -/

namespace Airbender.Delegation

/-- The RV delegation of each caller family: bigint `0x7CA`, G `0x7C8`, extended round `0x7C7`, Keccak `0x7CB`. -/
def Family.rvKind : Family → RV.DelegationKind
  | .bigint => .bigint
  | .blakeG => .blakeG
  | .blakeRound => .blakeRound
  | .keccak => .keccak

end Airbender.Delegation

namespace Airbender.Delegation.Caller
open Trace Arithmetic

/-- RV sibling of `decoderFields`: the four caller delegations (`.delegate k`, both GPR operands x0 by `RV.decode`) get
    the native caller metadata; every other instruction, the split Keccak-f1600 calls included, is rejected. -/
def rvDecoderFields : RV.Instr → Option (DecoderData Family)
  | .delegate .bigint => some ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | .delegate .blakeG => some ⟨.blakeG, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | .delegate .blakeRound => some ⟨.blakeRound, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | .delegate .keccak => some ⟨.keccak, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | _ => none

abbrev RVProgramEntry := Trace.RVProgramEntry Family

/-- RV sibling of `programImage`: caller entries read from the public ROM image and decoded by `RV.decode`. -/
noncomputable abbrev rvProgramImage := Trace.rvProgramImageWith rvDecoderFields

/-- RV sibling of `ProgramEntry.SourceWith before decoderFields`: the entry is the public table's entry at its PC, an
    aligned ROM word of `before` that `RV.decode` reads as an admitted caller delegation. -/
def RVSource (before : RV.State) (entry : RVProgramEntry) : Prop :=
  Trace.rvProgramEntryWith rvDecoderFields before entry.pc = some entry

/-- RV sibling of `query`: the same nine-column ADD/SUB decoder row (rs2 field = the full virtual CSR address). -/
def rvQuery {p : Nat} (entry : RVProgramEntry) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, 0, Requests.csr entry.data.family, 0, 0, 0, 0, 128]

/-- RV sibling of `decoderTable`: the modeled caller table, constructed from public RV entries. -/
def rvDecoderTable {p : Nat} [Fact p.Prime] (program : List RVProgramEntry) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.DelegationCaller"
  length := program.length
  row i := rvQuery (program.get i)
  index values := program.toArray.findIdx (fun entry => rvQuery entry == values)
  Spec values := ∃ entry ∈ program, values = rvQuery entry
  contains_iff := by
    intro values
    constructor
    · rintro ⟨i, equal⟩
      exact ⟨program.get i, List.get_mem _ _, equal⟩
    · rintro ⟨entry, member, equal⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      exact ⟨i, equal⟩ }

/-- RV sibling of `PCBinding`: caller PC effects tied to actual public RV decoding. Range queries prove the final word
    is canonical; the RV retirement (`nextInstr`, and any successful `RV.step` of the call) lands on it. -/
structure RVPCBinding (w : Nat → ZMod p) (before : RV.State) (program : List RVProgramEntry) : Prop where
  /-- The native starting PC locates one actual public caller instruction. -/
  instruction : ∃ entry ∈ program, RVSource before entry ∧ initialPC w = Word.ofBitVec entry.pc
  /-- Both final PC limbs are ranged by the imported lookup queries. -/
  bounded : (finalPC w).Bounded
  /-- The retained PC equations advance the decoded address by four. -/
  advances : (finalPC w).toBitVec = (initialPC w).toBitVec + 4
  /-- The RV retirement path, in any state at that PC. -/
  retire : ∀ s : RV.State, s.pc = (initialPC w).toBitVec → s.nextInstr.pc = (finalPC w).toBitVec
  /-- A successful `RV.step` from that PC, with the public ROM image, ends at the final PC. -/
  step : ∀ s t : RV.State, s.rom = before.rom → s.pc = (initialPC w).toBitVec → RV.step s = some t →
    t.pc = (finalPC w).toBitVec

/-- RV sibling of `Binding`: one actual public RV instruction, the delegation call `.delegate k` of the request's family
    (so `RV.step` at that PC is the call's effect, `RV.exec s (.delegate k)`), its full CSR request token, and a zero
    architectural destination word. These are conclusions; no selected instruction or desired result is assumed. -/
structure RVBinding (w : Nat → ZMod p) (before : RV.State) (program : List RVProgramEntry) : Prop where
  /-- Successful public decoding determines the invoked family and its delegation call. -/
  instruction : ∃ entry ∈ program, RVSource before entry ∧
    RV.decode entry.bits = some (.delegate entry.data.family.rvKind) ∧
    (∀ s : RV.State, s.rom = before.rom → s.pc = entry.pc →
      RV.step s = RV.exec s (.delegate entry.data.family.rvKind)) ∧
    (Requests.caller w).csr = Requests.csr entry.data.family
  /-- The virtual CSR read consumes the empty token. -/
  emptyRead : readToken w Requests.callerPort = (Requests.caller w).empty
  /-- The virtual CSR write issues this row's invocation clock. -/
  issuedWrite : writeToken AddSub.importedConstraintsTraceColumns w Requests.callerPort =
    (Requests.caller w).issued
  /-- The imported destination write contains zero. -/
  zeroDestination : destination w = ⟨0, 0⟩
  /-- The real source port addresses x0. -/
  sourceAddress : (sourceToken w).address = (Cell.register 0).addressCode
  /-- The real destination port addresses x0; the virtual CSR stays separate. -/
  destinationAddress : (destinationToken w).address = (Cell.register 0).addressCode
  /-- RV reads x0 as zero, and the native zero write to x0 leaves every RV state unchanged. -/
  registerEffects : ∀ state : RV.State,
    (Cell.register 0).readRV state = some 0 ∧
    (Cell.register 0).applyRV (destination w).toBitVec state = some state

end Airbender.Delegation.Caller
