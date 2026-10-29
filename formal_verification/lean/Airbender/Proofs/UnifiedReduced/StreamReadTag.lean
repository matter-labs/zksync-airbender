import Airbender.Proofs.UnifiedReduced.StreamDecoder

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- Standard unified instructions do not consume external stream words. -/
theorem standard_read_disabled {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.decoderFields instruction = some data) :
    data.mask.testBit 8 = false := by
  unfold UnifiedReduced.decoderFields at fields
  cases first : Trace.decoderFields instruction with
  | some original =>
    simp [first] at fields
    subst data
    have bound := (Trace.Proofs.decoder_field_bounds first).2
    have disabled : original.mask.testBit 8 = false := by
      norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
      omega
    cases family : original.family
    · simpa only [UnifiedReduced.arithmeticFields, family,
        DecoderData.mapFamily] using disabled
    · simp only [UnifiedReduced.arithmeticFields, family, DecoderData.mapFamily]
      split_ifs <;> decide +kernel
  | none =>
    cases second : JumpBranchSlt.decoderFields instruction with
    | some original =>
      simp [first, second] at fields
      subst data
      change (1024 * original.mask).testBit 8 = false
      norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
      omega
    | none =>
      cases third : ShiftBinop.decoderFields instruction with
      | none => simp [first, second, third] at fields
      | some original =>
        simp [first, second, third] at fields
        subst data
        change (32768 * original.mask).testBit 8 = false
        norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
        omega

/-- The ordinary, custom and modular registry preserves stream position. -/
theorem modular_read_disabled {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Modular.decoderFields instruction = some data) :
    data.mask.testBit 8 = false := by
  rcases Modular.Proofs.fields_cases fields with mixed | modular
  · rcases Mixed.Proofs.fields_cases mixed with standard | custom
    · exact standard_read_disabled standard
    · rcases UnifiedReduced.Proofs.custom_field_mask custom with mask | mask
      all_goals rw [mask]; decide +kernel
  · obtain ⟨opcode, rs1, rs2, rd, _, equal⟩ := Modular.Proofs.mop_cases modular
    rw [equal]
    exact Modular.Proofs.mop_high_flags opcode rs1 rs2 rd (1 : Fin 12)

/-- The native read selector equals the public metadata's read bit. -/
theorem native_read_tag [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) {entry : UnifiedReduced.ProgramEntry}
    (fields : Stream.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    Stream.isRead (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) =
      entry.data.mask.testBit 8 := by
  have flag := UnifiedReduced.Proofs.decoder_selectors hp core
    (field_bounds fields).2.1 query 8
  change w 19 = (if entry.data.mask.testBit 8 then 1 else 0) at flag
  change (w 19 == 1) = entry.data.mask.testBit 8
  rw [flag]
  cases entry.data.mask.testBit 8 <;> simp

/-- Native ordinary and modular cycles leave the stream counter unchanged. -/
theorem native_modular_read_disabled [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) {entry : UnifiedReduced.ProgramEntry}
    (fields : Modular.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    Stream.isRead (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) = false := by
  have combined : Stream.decoderFields entry.instruction = some entry.data := by
    simp [Stream.decoderFields, fields]
  rw [native_read_tag hp core combined query]
  exact modular_read_disabled fields

/-- Native caller selection excludes the external-read selector. -/
theorem native_caller_read_disabled [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 18)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) (active : w 4 = 1)
    (selected : Caller.Selected w) :
    Stream.isRead (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) = false := by
  have zero := UnifiedReduced.Proofs.dispatch_exclusive hp core active 7 selected 8 (by decide)
  change w 19 = 0 at zero
  change (w 19 == 1) = false
  simp [zero]

end Airbender.UnifiedReduced.Caller.Stream.Proofs
