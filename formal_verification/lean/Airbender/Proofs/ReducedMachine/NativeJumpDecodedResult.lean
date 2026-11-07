import Airbender.Proofs.ReducedMachine.NativeJumpReturn
import Airbender.Proofs.ReducedMachine.NativeJumpNumerics

namespace Airbender.ReducedMachine.NativeJumpResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Newly bound native base fields select original incoming PC or actual source. -/
theorem base_word {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    jumpBaseWord w = if entry.data.family then initialPCWord w else sourceWord w := by
  have decoded := NativeJumpDecoderProofs.decoded_fields fields query
  have actual := NativeJumpFieldProofs.base holds entry.data.family decoded.mask
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  cases choice : entry.data.family
  all_goals simp only [choice,Bool.false_eq_true,if_false,if_true] at low high ⊢
  all_goals simp at low high
  all_goals simp [jumpBaseWord,initialPCWord,sourceWord,source1,importedConstraintsMemoryPorts,
    Trace.WordColumns.evaluate,low,high]

/-- Every base/immediate bound in raw_result is discharged from original public
    PC/offset fields and the initialized actual first-read range. -/
theorem raw_target_result {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded) :
    (jumpRawTargetWord w).toBitVec = entry.data.family.base
      (initialPCWord w).toBitVec (sourceWord w).toBitVec+entry.data.immediate.toBitVec := by
  have decoded := NativeJumpDecoderProofs.decoded_fields fields query
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have pc : (initialPCWord w).Bounded := by rw [canonical]; exact Word.ofBitVec_bound _
  have base := base_word holds fields query
  have baseBound : (jumpBaseWord w).Bounded := by rw [base]; split <;> assumption
  have immediate := NativeJumpDecoderProofs.immediate_word fields query
  have immBound : (jumpImmediateWord w).Bounded := by
    rw [immediate]; exact (NativeJumpDecoderProofs.field_bounds fields).1
  have result := NativeJumpNumericalProofs.raw_result holds entry.data.family decoded.mask baseBound immBound
  rw [base,immediate] at result
  cases choice : entry.data.family <;> simpa [choice,JumpMode.base] using result

/-- Exact native cleanup, raw bit1 exclusion and final selection implement
    low-bit clearing at full RV32 width. No architectural result is assumed. -/
theorem cleared_target {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (jal : Bool) (mask : w 12 = (jumpMask jal : ZMod mersenne31Modulus)) :
    (finalPCWord w).toBitVec = (jumpRawTargetWord w).toBitVec &&& 0xfffffffe := by
  have cleanup := NativeJumpNumericalProofs.cleanup holds jal mask
  have bit1 := NativeJumpNumericalProofs.raw_bit1 holds jal mask
  have rawBound := NativeJumpNumericalProofs.raw_bounds holds
  have finalBound := (NativeJumpNumericalProofs.final_bounds holds jal mask).1
  have fieldBound : 4*((w 61).val / 4) < mersenne31Modulus := by
    have := cleanup.1; change _ < 2147483647; omega
  have low := congrArg ZMod.val cleanup.2.2
  rw [ZMod.val_natCast_of_lt fieldBound] at low
  have selected := NativeJumpFieldProofs.pc holds jal mask
  have lowField := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) selected
  have highField := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) selected
  have lo : w 13 = w 65 := by simpa [finalPC,importedConstraintsTraceColumns] using lowField
  have hi : w 14 = w 62 := by simpa [finalPC,importedConstraintsTraceColumns] using highField
  apply BitVec.eq_of_toNat_eq
  rw [clear_low_bit_toNat,Word.toBitVec_toNat rawBound,Word.toBitVec_toNat finalBound]
  change (w 13).val+65536*(w 14).val =
    ((w 61).val+65536*(w 62).val)-((w 61).val+65536*(w 62).val)%2
  rw [lo,hi,low]
  omega

/-- Initialized source bounds and original decoded parity connect the actual
    cleaned target to JAL or JALR, including full RV32 wrap and low-bit clearing. -/
theorem decoded_result {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    {before : Reference.RiscV.Sail.State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (source : entry.SourceWith before jumpDecoderFields) (query : decoderQuery w = entry.query)
    (readBound : (sourceWord w).Bounded) (aligned : (initialPCWord w).lo % 4 = 0) :
    JumpNumericalEffects w entry := by
  have decoded := NativeJumpDecoderProofs.decoded_fields source.fields query
  have returned := NativeJumpReturnProofs.candidate_result holds source.fields query aligned
  have raw := raw_target_result holds source.fields query readBound
  have rawBound := NativeJumpNumericalProofs.raw_bounds holds
  have cleaned := cleared_target holds entry.data.family decoded.mask
  have finalBound := NativeJumpNumericalProofs.final_bounds holds entry.data.family decoded.mask
  have rawWord : jumpRawTargetWord w = Word.ofBitVec
      (entry.data.family.base (initialPCWord w).toBitVec (sourceWord w).toBitVec+entry.data.immediate.toBitVec) := by
    apply Word.eq_of_value rawBound (Word.ofBitVec_bound _)
    rw [Word.ofBitVec_value,← raw,Word.toBitVec_toNat rawBound]
  have target : (finalPCWord w).toBitVec = entry.data.family.target
      (initialPCWord w).toBitVec (sourceWord w).toBitVec entry.data.immediate.toBitVec := by
    cases choice : entry.data.family
    · simpa [JumpMode.target,choice,raw] using cleaned
    · have parity := NativeJumpDecoderProofs.offset_even source choice
      have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
      change initialPCWord w = Word.ofBitVec entry.pc at canonical
      have pcBound : (initialPCWord w).Bounded := by rw [canonical]; exact Word.ofBitVec_bound _
      have immBound := (NativeJumpDecoderProofs.field_bounds source.fields).1
      have even : (jumpRawTargetWord w).toBitVec.toNat % 2 = 0 := by
        rw [raw]
        simp only [JumpMode.base,choice,if_true,BitVec.toNat_add,
          Word.toBitVec_toNat pcBound,Word.toBitVec_toNat immBound]
        unfold Word.value limbBase at *
        omega
      have noChange : (jumpRawTargetWord w).toBitVec &&& 0xfffffffe = (jumpRawTargetWord w).toBitVec := by
        apply BitVec.eq_of_toNat_eq
        rw [clear_low_bit_toNat,even,Nat.sub_zero]
      rw [cleaned,noChange,raw]
      simp [JumpMode.target,choice]
  have finalWord : finalPCWord w = Word.ofBitVec (entry.data.family.target
      (initialPCWord w).toBitVec (sourceWord w).toBitVec entry.data.immediate.toBitVec) := by
    apply Word.eq_of_value finalBound.1 (Word.ofBitVec_bound _)
    rw [Word.ofBitVec_value,← target,Word.toBitVec_toNat finalBound.1]
  exact ⟨returned.1,returned.2,rawWord,finalWord,finalBound⟩

end Airbender.ReducedMachine.NativeJumpResultProofs
