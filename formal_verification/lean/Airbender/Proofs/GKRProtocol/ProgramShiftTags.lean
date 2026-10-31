import Airbender.Proofs.GKRProtocol.PublicProgramCases
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths
import Airbender.Proofs.AddSub.ModularExternalDecoder
import Airbender.Proofs.ShiftBinop.Decoder

namespace Airbender.Compiler
open Airbender Trace Trace.NativeDecoder Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- The reduced filter retains the original full decoder projection. -/
theorem public_program_full_fields {config : ProgramRows.Config}
    {instruction : SailRV32.instruction} {data : DecoderData PooledFamily}
    (fields : config.fields instruction = some data) :
    AddSub.Modular.External.decoderFields instruction = some data := by
  cases config with
  | fullUnsigned => exact fields
  | reduced =>
    cases standard : AddSub.Modular.External.decoderFields instruction with
    | none => simp [ProgramRows.Config.fields, standard] at fields
    | some raw =>
      cases family : raw.family <;> simp_all [ProgramRows.Config.fields]

/-- The public Shift/Binop row retains its family-specific origin fields. -/
theorem public_program_shift_source {config : ProgramRows.Config}
    {initial : State} {entry : PooledProgramEntry}
    (origin : entry.SourceWith initial config.fields)
    (family : entry.data.family = .shiftBinop) :
    ∃ original : ProgramEntry Unit,
      original.SourceWith initial ShiftBinop.decoderFields ∧
      entry = original.mapFamily (fun _ => .shiftBinop) := by
  have full : entry.SourceWith initial AddSub.Modular.External.decoderFields :=
    ⟨origin.bytes, origin.decoded, public_program_full_fields origin.fields⟩
  rcases AddSub.Modular.External.Proofs.source_cases full with standard | branch | multiply | shift | memory
  · obtain ⟨original, _, equal⟩ := standard
    rw [equal] at family
    cases selected : original.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, pooledArithmeticFamily, selected] at family
  · obtain ⟨original, _, equal⟩ := branch
    rw [equal] at family
    cases family
  · obtain ⟨original, _, equal⟩ := multiply
    rw [equal] at family
    cases family
  · exact shift
  · obtain ⟨original, _, equal⟩ := memory
    rw [equal] at family
    cases family

/-- Arithmetic assertions fix both operation selector bits before helper use. -/
theorem shift_flags_of_assertions {w : Nat → ZMod babyBearModulus}
    (arithmetic : ∀ expression ∈ FlatOperation.constraints
      (ShiftBinop.importedConstraints (p := babyBearModulus)),
      expression.eval (Verification.environment w) = 0) :
    (w 11 = 0 ∨ w 11 = 1) ∧ (w 12 = 0 ∨ w 12 = 1) := by
  constructor
  · have flag := arithmetic _ (List.get_mem _ ⟨47, by rw [ShiftBinop.constraint_count]; decide⟩)
    simpa [ShiftBinop.importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag
  · have flag := arithmetic _ (List.get_mem _ ⟨48, by rw [ShiftBinop.constraint_count]; decide⟩)
    simpa [ShiftBinop.importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag

/-- Native definitions bind the five helper tags to the decoder selectors. -/
theorem shift_tag_equations_of_assertions {w : Nat → ZMod babyBearModulus}
    (arithmetic : ∀ expression ∈ FlatOperation.constraints
      (ShiftBinop.importedConstraints (p := babyBearModulus)),
      expression.eval (Verification.environment w) = 0) :
    w 55 = 8 * w 11 + 3 * w 12 ∧
      ∀ index : Fin 4, w (64 + 9 * index.val) = 9 * w 11 + w 10 * w 12 := by
  constructor
  · have equation := arithmetic _ (List.get_mem _ ⟨4, by rw [ShiftBinop.constraint_count]; decide⟩)
    simp [ShiftBinop.importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at equation
    linear_combination equation
  · intro index
    have equation := arithmetic _ (List.get_mem _
      ⟨13 + 9 * index.val, by rw [ShiftBinop.constraint_count]; have := index.isLt; omega⟩)
    fin_cases index <;>
      simp [ShiftBinop.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at equation <;> linear_combination equation

/-- Public decoder matching bounds both dynamic helper tags. -/
theorem public_shift_helper_tags
    {config : ProgramRows.Config} {initial : State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (w : Nat → ZMod babyBearModulus)
    (member : ProgramRows.maskRow (masks .shiftBinop) (ShiftBinop.decoderQuery w) ∈ columns .shiftBinop)
    (typed : (ShiftBinop.decoderQuery w)[0].val < 65536)
    (arithmetic : ∀ expression ∈ FlatOperation.constraints
      (ShiftBinop.importedConstraints (p := babyBearModulus)),
      expression.eval (Verification.environment w) = 0) :
    ((8 * w 11 + 3 * w 12 = 8) ∨ (8 * w 11 + 3 * w 12 = 3)) ∧
      ((9 * w 11 + w 10 * w 12 = 9) ∨
       (9 * w 11 + w 10 * w 12 = 4) ∨
       (9 * w 11 + w 10 * w 12 = 6) ∨
       (9 * w 11 + w 10 * w 12 = 7)) := by
  have bounded : ((ProgramRows.maskRow (masks .shiftBinop) (ShiftBinop.decoderQuery w)).head?.getD 0).val < 65536 := by
    simpa [ProgramRows.maskRow] using typed
  rcases unrolled_active_public_case setup .shiftBinop _ member bounded with
    ⟨entry, _, origin, family, query⟩ | ⟨_, _, _, impossible, _⟩
  · obtain ⟨original, shiftOrigin, rfl⟩ := public_program_shift_source origin family
    rw [NativeProgramSetup.unrolled_mask_eq setup .shiftBinop] at query
    have unmasked : ShiftBinop.decoderQuery w = original.query := by
      apply Vector.toList_inj.mp
      exact query
    have packed := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) unmasked
    have tag := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[7]) unmasked
    change (∑ i : Fin 2, (2 ^ i.val : Nat) * w ShiftBinop.importedConstraintsDecoderColumns.flags[i]) =
      (original.data.mask : ZMod babyBearModulus) at packed
    rw [Fin.sum_univ_two] at packed
    have packedValue : w 11 + 2 * w 12 = (original.data.mask : ZMod babyBearModulus) := by
      simpa [ShiftBinop.importedConstraintsDecoderColumns] using packed
    clear packed
    have packed := packedValue
    change w 10 = (original.data.funct3 : ZMod babyBearModulus) at tag
    obtain ⟨shift, binary⟩ := shift_flags_of_assertions arithmetic
    rcases ShiftBinop.Proofs.decoder_operation_tags shiftOrigin.fields with ⟨mask, tags⟩ | ⟨mask, tags⟩
    · rcases shift with shift | shift <;> rcases binary with binary | binary
      all_goals norm_num [babyBearModulus, shift, binary, mask] at packed
      all_goals try exact False.elim ((of_decide_eq_false rfl) packed)
      all_goals rcases tags with code | code | code | code
      all_goals simp only [shift, binary, tag, code]
      all_goals exact of_decide_eq_true rfl
    · rcases shift with shift | shift <;> rcases binary with binary | binary
      all_goals norm_num [babyBearModulus, shift, binary, mask] at packed
      all_goals try exact False.elim ((of_decide_eq_false rfl) packed)
      all_goals rcases tags with code | code | code
      all_goals simp only [shift, binary, tag, code]
      all_goals exact of_decide_eq_true rfl
  · cases impossible

end Airbender.Compiler
