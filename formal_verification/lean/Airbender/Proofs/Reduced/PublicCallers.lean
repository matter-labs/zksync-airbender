import Airbender.Proofs.Reduced.PublicBinding

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Every reduced native caller has an original typed extended-round source. -/
theorem reduced_public_caller (initial : State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4)
    (caller : ProgramRows.CallerEntry)
    (member : caller ∈ ProgramRows.callerProgramOf .reduced initial text) :
    ∃ entry ∈ FullUnsigned.entriesWith reducedCallerFields text,
      entry.SourceWith initial Delegation.Caller.decoderFields ∧
      caller.pc = entry.pc ∧ caller.instruction = entry.instruction ∧
      caller.query (p := babyBearModulus) = Delegation.Caller.query entry := by
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨pc, bytes, decoded⟩ := public_caller_data ProgramRows.Config.reduced.delegationCSR initial bits index selected
  have source := ProgramRows.Proofs.caller_sources .reduced initial text image size caller member
  obtain ⟨address, instruction, csr⟩ := source.csrShape
  have allowed : address.toNat = 0x7c7 :=
    ProgramRows.Proofs.reduced_delegation_csr (csr ▸ source.allowlisted)
  have addressValue : address = 0x7c7 := BitVec.eq_of_toNat_eq allowed
  let data : DecoderData Delegation.Family := ⟨.blakeRound, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  have metadata : Delegation.Caller.decoderFields caller.instruction = some data := by
    rw [instruction, addressValue]
    rfl
  have reducedMetadata : reducedCallerFields caller.instruction = some data := by
    rw [instruction, addressValue]
    rfl
  let entry : Delegation.Caller.ProgramEntry := ⟨caller.pc, caller.bits, caller.instruction, data⟩
  refine ⟨entry, ?_, ⟨source.bytes, source.decoded, metadata⟩, rfl, rfl, ?_⟩
  · apply List.mem_filterMap.mpr
    refine ⟨(bits, index), inText, ?_⟩
    simp only [decoded, reducedMetadata, bind, Option.bind]
    simp only [entry, pc, bytes]
    rfl
  · simp only [ProgramRows.CallerEntry.query, Delegation.Caller.query, entry, data, csr, addressValue]
    rfl

/-- The native packed ADD/SUB query determines every actual selector. -/
theorem addsub_packed_selector [Fact p.Prime] (hp : FieldCapacity.NoWrap p limbBase)
    {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (mask : Nat) (small : mask < 512)
    (packed : (Delegation.Caller.nativeQuery w)[8] = (mask : ZMod p)) :
    ∀ i : Fin 9, w AddSub.importedConstraintsDecoderColumns.flags[i] =
      if mask.testBit i.val then 1 else 0 := by
  have flags := (AddSub.Proofs.local_flags core).2
  have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
      w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
    intro i
    have bit := flags i
    fin_cases i <;> simpa using bit
  change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
    (mask : ZMod p) at packed
  exact unpack_decoder_bits (by dsimp [limbBase] at hp; omega) small boolean packed

end Airbender.Compiler.MachineTargets.Proofs
