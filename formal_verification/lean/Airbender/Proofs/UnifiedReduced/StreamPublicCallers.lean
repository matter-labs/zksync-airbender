import Airbender.Proofs.UnifiedReduced.StreamPublicBinding

namespace Airbender.Compiler.MachineTargets.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- A retained virtual caller preserves its text position and pure Sail decode. -/
theorem public_caller_data (allowed : Nat → Bool) (initial : State)
    (bits : BitVec 32) (index : Nat) {caller : ProgramRows.CallerEntry}
    (selected : ProgramRows.callerEntryWith allowed initial bits index = some caller) :
    caller.pc = BitVec.ofNat 32 (4 * index) ∧ caller.bits = bits ∧
      SailRV32.Functions.encdec_backwards bits = .pure caller.instruction := by
  unfold ProgramRows.callerEntryWith at selected
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | impure call continuation => simp [decoded] at selected
  | pure instruction =>
    simp only [decoded, bind, Option.bind] at selected
    split at selected
    next address source destination shape =>
      split at selected
      next active =>
        cases selected
        exact ⟨rfl, rfl, rfl⟩
      next inactive => simp at selected
    next unsupported => simp at selected

/-- Public virtual caller membership supplies the exact typed caller query. -/
theorem unified_public_caller
    (initial : State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4)
    (caller : ProgramRows.CallerEntry)
    (member : caller ∈ UnifiedProgramRows.callerProgramOf initial text) :
    ∃ entry ∈ FullUnsigned.entriesWith Delegation.Caller.decoderFields text,
      entry.SourceWith initial Delegation.Caller.decoderFields ∧
      caller.pc = entry.pc ∧ caller.instruction = entry.instruction ∧
      caller.query (p := babyBearModulus) = Delegation.Caller.query entry := by
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨pc, bytes, decoded⟩ := public_caller_data UnifiedProgramRows.delegationCSR initial bits index selected
  have source := UnifiedProgramRows.Proofs.caller_sources initial text image size caller member
  obtain ⟨address, instruction, csr⟩ := source.csrShape
  obtain ⟨data, fields, csrKind⟩ := unified_csr_fields address (csr ▸ source.allowlisted)
  let entry : Delegation.Caller.ProgramEntry := ⟨caller.pc, caller.bits, caller.instruction, data⟩
  have metadata : Delegation.Caller.decoderFields caller.instruction = some data := instruction ▸ fields
  refine ⟨entry, ?_, ⟨source.bytes, source.decoded, metadata⟩, rfl, rfl, ?_⟩
  · apply List.mem_filterMap.mpr
    refine ⟨(bits, index), inText, ?_⟩
    simp only [decoded, metadata, bind, Option.bind]
    simp only [entry, pc, bytes]
    rfl
  · simp only [ProgramRows.CallerEntry.query, Delegation.Caller.query, entry, ← csrKind, csr]

/-- Every text-derived typed caller retains its public Sail source. -/
theorem text_caller_sources {Family : Type}
    (fields : SailRV32.instruction → Option (DecoderData Family))
    (initial : State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    ∀ entry ∈ FullUnsigned.entriesWith fields text, entry.SourceWith initial fields := by
  intro entry member
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  have found : text[index]? = some bits := List.mk_mem_zipIdx_iff_getElem?.mp inText
  have indexBound : index < text.length := by
    by_contra notBound
    have : text[index]? = none := by simp [Nat.le_of_not_gt notBound]
    rw [this] at found
    contradiction
  have value : text[index] = bits := by simpa [indexBound] using found
  have bytes : (Cell.ram (BitVec.ofNat 32 (4 * index))).read initial = .ok bits initial := by
    simpa only [value] using ROM.Proofs.bytes_of_text_image initial text image size ⟨index, indexBound⟩
  cases decoded : SailRV32.Functions.encdec_backwards bits with
  | impure call continuation => simp [decoded] at selected
  | pure instruction =>
    cases metadata : fields instruction with
    | none => simp [decoded, metadata] at selected
    | some data =>
      simp only [decoded, metadata, bind, Option.bind] at selected
      cases selected
      exact ⟨bytes, by rw [decoded]; rfl, metadata⟩

/-- The typed caller registry has a public stateful program image. -/
theorem unified_caller_image (initial : State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4) :
    Delegation.Caller.programImage initial
      ((FullUnsigned.entriesWith Delegation.Caller.decoderFields text).map ProgramEntry.pc) =
      some (FullUnsigned.entriesWith Delegation.Caller.decoderFields text) :=
  Airbender.Compiler.PublicProgram.image_run _
    (text_caller_sources Delegation.Caller.decoderFields initial text image size)

end Airbender.Compiler.MachineTargets.Proofs
