import Airbender.Review.Circuits.UnifiedReduced.Decoder
import Airbender.Proofs.UnifiedReduced
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.JumpBranchSlt.Decoder
import Airbender.Proofs.ShiftBinop.Decoder

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem decoder_field_bounds {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Trace.UnifiedFamily}
    (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 524288 ∧ data.funct3 < 55 := by
  unfold decoderFields at fields
  cases first : Trace.decoderFields instruction with
  | some original =>
    simp [first] at fields
    subst data
    have bounds := Trace.Proofs.decoder_field_bounds first
    change original.immediate.Bounded ∧ _ ∧ _
    refine ⟨bounds.1, ?_, ?_⟩
    · dsimp [arithmeticFields, Trace.DecoderData.mapFamily]
      cases original.family <;> simp only <;> (try split_ifs) <;> omega
    · have tag : original.funct3 = 0 := by
        unfold Trace.decoderFields at first
        split at first
        all_goals try split at first
        all_goals first
          | (simp only [Option.some.injEq] at first
             subst original
             first | rfl | (unfold Trace.arithmeticFields; split <;> rfl))
          | (cases first)
      change original.funct3 < 55
      omega
  | none =>
    cases second : JumpBranchSlt.decoderFields instruction with
    | some original =>
      simp [first, second] at fields
      subst data
      have bounds := JumpBranchSlt.Proofs.decoder_field_bounds second
      change original.immediate.Bounded ∧ 1024 * original.mask < 524288 ∧ original.funct3 < 55
      exact ⟨bounds.1, by omega, by omega⟩
    | none =>
      cases third : ShiftBinop.decoderFields instruction with
      | none => simp [first, second, third] at fields
      | some original =>
        simp [first, second, third] at fields
        subst data
        have bounds := ShiftBinop.Proofs.decoder_field_bounds third
        change original.immediate.Bounded ∧ 32768 * original.mask < 524288 ∧ _
        refine ⟨bounds.1, by omega, ?_⟩
        dsimp [binaryFields, Trace.DecoderData.mapFamily]
        split_ifs <;> omega

theorem decoder_selectors {p : Nat} [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (small : entry.data.mask < 524288) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 19) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := local_flags h ⟨i.val + 1, by omega⟩
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 19, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod p) at packed
  exact Trace.Proofs.unpack_decoder_bits_general (by simpa using hp)
    (by simpa using small) boolean packed

theorem fetched {p : Nat} [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before := by
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member member
  have source := Trace.Proofs.run_program_sources image entry present
  have bounds := decoder_field_bounds source.fields
  exact ⟨entry, source, query, decoder_selectors hp h bounds.2.1 query⟩

end Airbender.UnifiedReduced.Proofs
