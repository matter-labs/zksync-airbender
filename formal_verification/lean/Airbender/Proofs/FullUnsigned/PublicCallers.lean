import Airbender.Proofs.FullUnsigned.PublicBinding

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The full native allowlist has five caller forms after the public exclusion. -/
theorem unrolled_full_csr_cases (address : BitVec 12)
    (allowed : ProgramRows.Config.fullUnsigned.delegationCSR address.toNat = true)
    (excluded : address.toNat ≠ 0x7cb) :
    address = 0x7c7 ∨ address = 0x7ca ∨ address = 0x7cc ∨
      address = 0x7cd ∨ address = 0x7ce := by
  have values : address.toNat = 0x7c7 ∨ address.toNat = 0x7ca ∨
      address.toNat = 0x7cc ∨ address.toNat = 0x7cd ∨ address.toNat = 0x7ce := by
    unfold ProgramRows.Config.delegationCSR at allowed
    split at allowed <;> simp_all
  rcases values with equal | equal | equal | equal | equal
  all_goals first
    | exact Or.inl (BitVec.eq_of_toNat_eq equal)
    | exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq equal))
    | exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq equal)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq equal))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq equal))))

/-- Every full native caller has an original standard or split Sail source. -/
theorem unrolled_full_public_caller (initial : State) (text : List (BitVec 32))
    (image : ROM.TextImage initial text) (size : text.length ≤ ROM.limit / 4)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (caller : ProgramRows.CallerEntry)
    (member : caller ∈ ProgramRows.callerProgramOf .fullUnsigned initial text) :
    (∃ entry ∈ FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text,
      entry.SourceWith initial Delegation.Caller.decoderFields ∧
      caller.pc = entry.pc ∧ caller.instruction = entry.instruction ∧
      caller.query (p := babyBearModulus) = Delegation.Caller.query entry) ∨
    (∃ entry ∈ FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text,
      entry.SourceWith initial Keccak.Split.Caller.decoderFields ∧
      caller.pc = entry.pc ∧ caller.instruction = entry.instruction ∧
      caller.query (p := babyBearModulus) = Keccak.Split.Caller.query entry) := by
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨pc, bytes, decoded⟩ := public_caller_data
    ProgramRows.Config.fullUnsigned.delegationCSR initial bits index selected
  have source := ProgramRows.Proofs.caller_sources .fullUnsigned initial text image size caller member
  obtain ⟨address, instruction, csr⟩ := source.csrShape
  have retained {Family : Type} (fields : SailRV32.instruction → Option (DecoderData Family))
      (data : DecoderData Family) (metadata : fields caller.instruction = some data) :
      (⟨caller.pc, caller.bits, caller.instruction, data⟩ : ProgramEntry Family) ∈
        FullUnsigned.entriesWith fields text := by
    apply List.mem_filterMap.mpr
    refine ⟨(bits, index), inText, ?_⟩
    simp only [decoded, metadata, bind, Option.bind]
    simp only [pc, bytes]
    rfl
  have standard (data : DecoderData Delegation.Family)
      (metadata : FullUnsigned.standardDecoderFields caller.instruction = some data)
      (request : Delegation.Requests.csr data.family = caller.csr) :
      ∃ entry ∈ FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text,
        entry.SourceWith initial Delegation.Caller.decoderFields ∧
        caller.pc = entry.pc ∧ caller.instruction = entry.instruction ∧
        caller.query (p := babyBearModulus) = Delegation.Caller.query entry := by
    refine ⟨⟨caller.pc, caller.bits, caller.instruction, data⟩,
      retained _ data metadata, ⟨source.bytes, source.decoded,
        (unrolled_full_caller_metadata metadata).1⟩, rfl, rfl, ?_⟩
    simp only [ProgramRows.CallerEntry.query, Delegation.Caller.query, request]
  have split (kind : Keccak.Split.Kind)
      (chosen : Keccak.Split.Caller.kindOfCSR caller.csr = some kind) :
      ∃ entry ∈ FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text,
        entry.SourceWith initial Keccak.Split.Caller.decoderFields ∧
        caller.pc = entry.pc ∧ caller.instruction = entry.instruction ∧
        caller.query (p := babyBearModulus) = Keccak.Split.Caller.query entry := by
    have original := Keccak.Split.Caller.Proofs.source_of_native initial caller kind source chosen
    refine ⟨Keccak.Split.Caller.Proofs.fromNative caller kind,
      retained _ _ original.fields, original, rfl, rfl, ?_⟩
    exact (Keccak.Split.Caller.Proofs.query_from_native caller kind chosen).symm
  have cases := unrolled_full_csr_cases address (csr ▸ source.allowlisted)
    (by simpa only [← csr] using excluded caller member)
  rcases cases with equal | equal | equal | equal | equal
  · exact Or.inl (standard ⟨.blakeRound, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
      (by rw [instruction, equal]; rfl) (by rw [csr, equal]; rfl))
  · exact Or.inl (standard ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
      (by rw [instruction, equal]; rfl) (by rw [csr, equal]; rfl))
  · exact Or.inr (split .thetaRho (by rw [csr, equal]; rfl))
  · exact Or.inr (split .columnParity (by rw [csr, equal]; rfl))
  · exact Or.inr (split .chi5 (by rw [csr, equal]; rfl))

end Airbender.Compiler.MachineTargets.Proofs
