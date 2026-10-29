import Airbender.Proofs.UnifiedReduced.StreamROMSupportedExecution
import Airbender.Proofs.UnifiedReduced.StreamROMInitialization
import Airbender.Proofs.GKRProtocol.PublicAcceptedRows

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Standard unified instructions do not select a delegation caller. -/
theorem standard_caller_disabled {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.decoderFields instruction = some data) :
    data.mask.testBit 7 = false := by
  unfold UnifiedReduced.decoderFields at fields
  cases first : Trace.decoderFields instruction with
  | some original =>
    simp [first] at fields
    subst data
    have bound := (Trace.Proofs.decoder_field_bounds first).2
    have disabled : original.mask.testBit 7 = false := by
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
      change (1024 * original.mask).testBit 7 = false
      norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
      omega
    | none =>
      cases third : ShiftBinop.decoderFields instruction with
      | none => simp [first, second, third] at fields
      | some original =>
        simp [first, second, third] at fields
        subst data
        change (32768 * original.mask).testBit 7 = false
        norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
        omega

/-- The ordinary, custom and modular registry clears the caller selector. -/
theorem modular_caller_disabled {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Modular.decoderFields instruction = some data) :
    data.mask.testBit 7 = false := by
  rcases Modular.Proofs.fields_cases fields with mixed | modular
  · rcases Mixed.Proofs.fields_cases mixed with standard | custom
    · exact standard_caller_disabled standard
    · rcases UnifiedReduced.Proofs.custom_field_mask custom with mask | mask
      all_goals rw [mask]; decide +kernel
  · obtain ⟨opcode, rs1, rs2, rd, _, equal⟩ := Modular.Proofs.mop_cases modular
    rw [equal]
    exact Modular.Proofs.mop_high_flags opcode rs1 rs2 rd (0 : Fin 12)

/-- No ordinary combined-registry instruction sets the native caller bit. -/
theorem stream_caller_disabled {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Stream.decoderFields instruction = some data) :
    data.mask.testBit 7 = false := by
  rcases fields_cases fields with modular | external
  · exact modular_caller_disabled modular
  · rcases external_fields_cases external with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    all_goals norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]

/-- An explicit packed decoder query determines each native selector. -/
theorem selector_of_packed_query [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mask : Nat) (small : mask < 524288) (query : (decoderQuery w)[8] = (mask : ZMod p)) :
    ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
      if mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 19) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := UnifiedReduced.Proofs.local_flags core ⟨i.val + 1, by omega⟩
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  change (∑ i : Fin 19, (2 ^ i.val : Nat) * bits i) = (mask : ZMod p) at query
  exact unpack_decoder_bits_general (by simpa using hp) (by simpa using small) boolean query

end Airbender.UnifiedReduced.Caller.Stream.Proofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail NativeDecoder
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The imported unified decoder retains all nine query fields. -/
theorem unified_mask_row [Fact p.Prime]
    (mask : ProgramRows.Mask) (binding : mask.columns = unifiedSetup.columnsMask)
    (row : Vector (ZMod p) 9) : ProgramRows.maskRow mask row = row.toList := by
  have full : mask.columns = #[true, true, true, true, true, true, true, true, true] := binding
  have eta : row = #v[row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8]] := by
    ext i bound
    interval_cases i <;> rfl
  rw [eta]
  simp [ProgramRows.maskRow, full]

/-- Equality of complete imported unified rows preserves the full query. -/
theorem unified_mask_query [Fact p.Prime]
    (mask : ProgramRows.Mask) (binding : mask.columns = unifiedSetup.columnsMask)
    {one two : Vector (ZMod p) 9}
    (equal : ProgramRows.maskRow mask one = ProgramRows.maskRow mask two) : one = two := by
  rw [unified_mask_row mask binding, unified_mask_row mask binding] at equal
  ext i bound
  have atIndex := congrArg (fun values : List (ZMod p) => values[i]?.getD 0) equal
  simpa [bound] using atIndex

/-- Every unified virtual caller has a typed reference decoder entry. -/
theorem unified_csr_fields (address : BitVec 12)
    (allowed : UnifiedProgramRows.delegationCSR address.toNat = true) :
    ∃ data : DecoderData Delegation.Family,
      Delegation.Caller.decoderFields (.CSRReg (address, .Regidx 0, .Regidx 0, .CSRRW)) = some data ∧
      Delegation.Requests.csr data.family = address.toNat := by
  have values : address.toNat = 0x7c7 ∨ address.toNat = 0x7c8 ∨
      address.toNat = 0x7ca ∨ address.toNat = 0x7cb := by
    unfold UnifiedProgramRows.delegationCSR at allowed
    split at allowed <;> simp_all
  have cases : address = 0x7c7 ∨ address = 0x7c8 ∨ address = 0x7ca ∨ address = 0x7cb := by
    rcases values with equal | equal | equal | equal
    all_goals first | exact Or.inl (BitVec.eq_of_toNat_eq equal) |
      exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq equal)) |
      exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq equal))) |
      exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq equal)))
  rcases cases with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl⟩

end Airbender.Compiler.MachineTargets.Proofs
