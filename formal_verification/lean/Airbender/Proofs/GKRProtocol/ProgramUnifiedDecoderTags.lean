import Airbender.Proofs.GKRProtocol.PublicProgramCases
import Airbender.Proofs.GKRProtocol.NativePublicDecoder
import Airbender.Proofs.UnifiedReduced.StreamDecoder

namespace Airbender.Compiler
open Airbender Trace Trace.NativeDecoder Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem ordinary_tag_zero {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields instruction = some data) : data.funct3 = 0 := by
  unfold Trace.decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals first
    | (simp only [Option.some.injEq] at fields
       subst data
       first | rfl | (unfold Trace.arithmeticFields; split <;> rfl))
    | (cases fields)

private theorem standard_unified_tags {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.decoderFields instruction = some data) :
    data.funct3 < 55 ∧ data.funct3 ≠ 46 := by
  unfold UnifiedReduced.decoderFields at fields
  cases first : Trace.decoderFields instruction with
  | some original =>
    simp [first] at fields
    subst data
    change original.funct3 < 55 ∧ original.funct3 ≠ 46
    rw [ordinary_tag_zero first]
    exact of_decide_eq_true rfl
  | none =>
    cases second : JumpBranchSlt.decoderFields instruction with
    | some original =>
      simp [first, second] at fields
      subst data
      have small := (JumpBranchSlt.Proofs.decoder_field_bounds second).2.2
      change original.funct3 < 55 ∧ original.funct3 ≠ 46
      omega
    | none =>
      cases third : ShiftBinop.decoderFields instruction with
      | none => simp [first, second, third] at fields
      | some original =>
        simp [first, second, third] at fields
        subst data
        have small := (ShiftBinop.Proofs.decoder_field_bounds third).2.2
        dsimp [UnifiedReduced.binaryFields, DecoderData.mapFamily]
        split_ifs <;> omega

private theorem custom_unified_tags {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.customDecoderFields instruction = some data) :
    data.funct3 < 55 ∧ data.funct3 ≠ 46 := by
  cases instruction with
  | ZIMOP_MOP_RR value =>
    rcases value with ⟨mop, rs2, rs1, rd⟩
    cases rs2; cases rs1; cases rd
    simp only [UnifiedReduced.customDecoderFields] at fields
    split at fields
    · cases fields; exact of_decide_eq_true rfl
    · cases fields
  | ZIMOP_MOP_R value =>
    rcases value with ⟨mop, rs1, rd⟩
    cases rs1; cases rd
    simp only [UnifiedReduced.customDecoderFields] at fields
    split at fields
    · cases fields
    · cases found : UnifiedReduced.customRotationTag mop with
      | none => simp only [found, bind, Option.bind] at fields; cases fields
      | some tag =>
        simp only [found, bind, Option.bind, Option.some.injEq] at fields
        subst data
        change tag < 55 ∧ tag ≠ 46
        unfold UnifiedReduced.customRotationTag at found
        split_ifs at found <;> cases found <;> exact of_decide_eq_true rfl
  | _ => cases fields

private theorem modular_unified_tags {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.Modular.decoderFields instruction = some data) :
    data.funct3 < 55 ∧ data.funct3 ≠ 46 := by
  rcases UnifiedReduced.Modular.Proofs.fields_cases fields with mixed | modular
  · rcases UnifiedReduced.Mixed.Proofs.fields_cases mixed with standard | custom
    · exact standard_unified_tags standard
    · exact custom_unified_tags custom
  · obtain ⟨opcode, rs1, rs2, rd, _, rfl⟩ := UnifiedReduced.Modular.Proofs.mop_cases modular
    unfold UnifiedReduced.Modular.mopData AddSub.Modular.nativeData Trace.arithmeticFields DecoderData.mapFamily
    split <;> exact of_decide_eq_true rfl

/-- Every public unified instruction uses an operation tag outside the decoder tag. -/
theorem public_unified_field_tags {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : UnifiedProgramRows.decoderFields instruction = some data) :
    data.funct3 < 55 ∧ data.funct3 ≠ 46 := by
  unfold UnifiedProgramRows.decoderFields at fields
  split at fields
  · split at fields
    · obtain ⟨original, parsed, rfl⟩ := Option.map_eq_some_iff.mp fields
      change original.funct3 < 55 ∧ original.funct3 ≠ 46
      rcases NonDeterminism.Proofs.fields_cases parsed with standard | read | hint
      · rw [ordinary_tag_zero standard]; exact of_decide_eq_true rfl
      · obtain ⟨_, _, _, rfl⟩ := read; exact of_decide_eq_true rfl
      · obtain ⟨_, _, _, rfl⟩ := hint; exact of_decide_eq_true rfl
    · exact modular_unified_tags fields
  · exact modular_unified_tags fields

/-- Public decoder matching fixes the native operation tag without a witness premise. -/
theorem public_unified_operation
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (w : Nat → Source.BaseField)
    (member : ProgramRows.maskRow mask (UnifiedReduced.decoderQuery w) ∈ columns)
    (typed : (UnifiedReduced.decoderQuery w)[0].val < 65536) : w 10 ≠ 46 := by
  have bounded : ((ProgramRows.maskRow mask (UnifiedReduced.decoderQuery w)).head?.getD 0).val < 65536 := by
    simpa [ProgramRows.maskRow] using typed
  rcases unified_active_public_case setup _ member bounded with
    ⟨ordinary, _, origin, query⟩ | ⟨caller, _, _, query⟩
  · rw [NativeProgramSetup.unified_mask_eq setup] at query
    have unmasked : UnifiedReduced.decoderQuery w = ordinary.query := Vector.toList_inj.mp query
    have tag := congrArg (fun q : Vector Source.BaseField 9 => q[7]) unmasked
    change w 10 = (ordinary.data.funct3 : Source.BaseField) at tag
    rw [tag]
    have tags := public_unified_field_tags origin.fields
    intro wrong
    have equal := congrArg ZMod.val wrong
    have small : ordinary.data.funct3 < babyBearModulus := by dsimp [babyBearModulus]; omega
    have value : (ordinary.data.funct3 : Source.BaseField).val = ordinary.data.funct3 :=
      ZMod.val_natCast_of_lt small
    have fortySix : (46 : Source.BaseField).val = 46 := by exact of_decide_eq_true rfl
    rw [value, fortySix] at equal
    exact tags.2 equal
  · rw [NativeProgramSetup.unified_mask_eq setup] at query
    have unmasked : UnifiedReduced.decoderQuery w = caller.query := Vector.toList_inj.mp query
    have tag := congrArg (fun q : Vector Source.BaseField 9 => q[7]) unmasked
    change w 10 = 0 at tag
    rw [tag]
    exact of_decide_eq_true rfl

end Airbender.Compiler
