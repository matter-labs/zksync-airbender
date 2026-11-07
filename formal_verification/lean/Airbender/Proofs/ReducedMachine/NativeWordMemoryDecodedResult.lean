import Airbender.Proofs.ReducedMachine.NativeWordMemoryPreservation
import Airbender.Proofs.ReducedMachine.NativeWordMemoryPC
import Airbender.Review.Circuits.ReducedMachine.WordMemoryResult

namespace Airbender.ReducedMachine.NativeWordMemoryResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original immediate decoding and the initialized actual source discharge
    every internal effective-address input bound. -/
theorem effective_address {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded) :
    wordMemoryAddressWord w = Word.ofBitVec ((sourceWord w).toBitVec+entry.data.immediate.toBitVec) := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have immediate := NativeWordMemoryDecoderProofs.immediate_word fields query
  have bound : (wordMemoryImmediateWord w).Bounded := by
    rw [immediate]; exact (NativeWordMemoryDecoderProofs.field_bounds fields).1
  have actual := NativeWordMemoryNumericalProofs.address_result holds entry.data.family decoded.mask source bound
  rw [immediate] at actual
  have output := NativeWordMemoryNumericalProofs.address_bounds holds
  apply Word.eq_of_value output (Word.ofBitVec_bound _)
  rw [Word.ofBitVec_value,← actual,Word.toBitVec_toNat output]

/-- Canonical exact fixed-ROM output, including the shadow query on RAM loads. -/
theorem rom_word {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) :
    (⟨(w 66).val,(w 67).val⟩ : Word) =
      wordMemoryROMWord (((w 61).val+65536*((w 62).val%64))/4) := by
  have actual := (NativeWordMemoryShapeProofs.load_address holds mask).2.2.2
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  simp only [Vector.getElem_map] at low high
  have bounds := NativeWordMemoryTableValues.rom_value_bounds (((w 61).val+65536*((w 62).val%64))/4)
  have small : 65536 < mersenne31Modulus := by decide
  apply congrArg₂ Word.mk
  · change w 66 = _ at low
    rw [low,ZMod.val_natCast_of_lt (lt_trans bounds.1 small)]
  · change w 67 = _ at high
    rw [high,ZMod.val_natCast_of_lt (lt_trans bounds.2 small)]

theorem load_candidate {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) :
    (⟨(w 116).val,(w 117).val⟩ : Word) = wordMemoryLoadWord w := by
  have actual := (NativeWordMemoryAccessProofs.load_access holds mask).candidate
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  have selection := (NativeWordMemoryShapeProofs.load_address holds mask).2.2.1
  by_cases inside : (w 62).val < 64
  · have flag : w 64 = 0 := by simpa [inside] using selection
    have lo : w 116 = w 66 := by simpa [flag] using low
    have hi : w 117 = w 67 := by simpa [flag] using high
    simpa [wordMemoryLoadWord,wordMemoryAddressWord,Word.value,limbBase,inside,lo,hi,Nat.mod_eq_of_lt inside] using rom_word holds mask
  · have flag : w 64 = 1 := by simpa [inside] using selection
    have lo : w 116 = w 37 := by simpa [flag] using low
    have hi : w 117 = w 38 := by simpa [flag] using high
    simp [wordMemoryLoadWord,wordMemoryAddressWord,inside,wordMemorySecondWord,lo,hi]

/-- SW writes the full earlier second source even though its decoded dummy rd
    is zero; LW alone masks its derived selected result using original rd/x0. -/
theorem written_result {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : wordMemoryWrittenWord w = wordMemoryResult w entry := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  cases mode : entry.data.family
  · have mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have actual := (NativeWordMemoryAccessProofs.load_access holds mask).written
    have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
    have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
    have zero : w 8 = (if entry.data.rd = 0 then 1 else 0) := decoded.zero
    by_cases discard : entry.data.rd = 0
    · have flag : w 8 = 1 := by rw [if_pos discard] at zero; exact zero
      simp [flag] at low high
      simp [wordMemoryResult,mode,discard,wordMemoryWrittenWord,low,high]
    · have flag : w 8 = 0 := by rw [if_neg discard] at zero; exact zero
      have lo : w 43 = w 116 := by simpa [flag] using low
      have hi : w 44 = w 117 := by simpa [flag] using high
      rw [wordMemoryResult,mode]
      change wordMemoryWrittenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else wordMemoryLoadWord w
      rw [if_neg discard]
      simpa only [wordMemoryWrittenWord,lo,hi] using load_candidate holds mask
  · have mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have actual := (NativeWordMemoryAccessProofs.store_access holds mask).written
    have low : w 43 = w 37 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
    have high : w 44 = w 38 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
    simp [wordMemoryResult,mode,wordMemoryWrittenWord,wordMemorySecondWord,low,high]

/-- Internal assembly; trace induction and public image membership discharge
    source bounds/alignment before the public numerical result is exposed. -/
theorem decoded_result {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded)
    (aligned : (initialPCWord w).lo%4 = 0) : WordMemoryNumericalEffects w entry := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  have shape : (wordMemoryAddressWord w).value%4 = 0 ∧
      (entry.data.family = true → 4194304 ≤ (wordMemoryAddressWord w).value) := by
    cases mode : entry.data.family
    · have mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
      exact ⟨(NativeWordMemoryShapeProofs.load_address holds mask).2.1,by intro impossible; cases impossible⟩
    · have mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
      have actual := NativeWordMemoryShapeProofs.store_address holds mask
      exact ⟨actual.2.2,fun _ => actual.2.1⟩
  have pc := NativeWordMemoryPCProofs.selected_pc_successor holds fields query aligned
  exact ⟨NativeWordMemoryPortProofs.addresses holds fields query,effective_address holds fields query source,
    shape.1,shape.2,written_result holds fields query,pc.1,pc.2⟩

end Airbender.ReducedMachine.NativeWordMemoryResultProofs
