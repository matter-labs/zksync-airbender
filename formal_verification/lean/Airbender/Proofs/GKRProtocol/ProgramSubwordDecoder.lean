import Airbender.Proofs.GKRProtocol.ProgramSubwordSetup
import Airbender.Proofs.GKRProtocol.NativePublicDecoder
import Airbender.Proofs.Tables.SubwordCharacterization

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler Airbender.Trace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem data_row_tag (key lo hi tag : Nat) :
    (((Verification.subwordDataRow key lo hi tag).map
      (fun value : Nat => (value : Source.BaseField))).toList.getLast?.getD 0) = (tag : Source.BaseField) := by
  simp [Verification.subwordDataRow]

/-- Fixed helpers and both public subword ROM views exclude the decoder tag. -/
theorem subword_prefix_not_decoder (wordAt : Nat → BitVec 32) (index : Fin 13238273) :
    (((Verification.subwordNativeRow wordAt index).map
      (fun value : Nat => (value : Source.BaseField))).toList.getLast?.getD 0) ≠ 46 := by
  rw [Verification.subwordNativeRow_eq_reference]
  unfold Verification.referenceSubwordRow Verification.subwordRow
  dsimp only
  split
  · rw [data_row_tag]; exact of_decide_eq_true rfl
  · split
    · rw [data_row_tag]; exact of_decide_eq_true rfl
    · split
      · rw [data_row_tag]; exact of_decide_eq_true rfl
      · split
        · rw [data_row_tag]; exact of_decide_eq_true rfl
        · split
          · rw [data_row_tag]; exact of_decide_eq_true rfl
          · split
            · rw [data_row_tag]; exact of_decide_eq_true rfl
            · rw [data_row_tag]; exact of_decide_eq_true rfl

/-- A typed decoder query selects a supplied public subword decoder row. -/
theorem subword_decoder_member (decoder : List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (index : Nat)
    (widths : ∀ row ∈ decoder, row.length = 8) (payload : List Source.BaseField)
    (payloadWidth : payload.length = 8)
    (same : ProgramSetup.packTagged 9 46 payload = subwordRows decoder wordAt index)
    (active : payload.head? ≠ some (-1)) : payload ∈ decoder := by
  unfold subwordRows at same
  split at same
  next bounded =>
    apply False.elim
    apply subword_prefix_not_decoder wordAt ⟨index, bounded⟩
    rw [← same]
    simp [ProgramSetup.packTagged]
  next outside =>
    split at same
    next decoderRegion =>
      have rowWidth : (decoder[index - 13238273]?.getD (ProgramSetup.decoderPadding 8)).length = 8 := by
        cases found : decoder[index - 13238273]? with
        | none => simp [ProgramSetup.decoderPadding]
        | some row => simpa only [found, Option.getD_some] using widths row (List.mem_of_getElem? found)
      have equal := ProgramSetup.packTagged_injective 9 (46 : Source.BaseField) payload _
        (payloadWidth.trans rowWidth.symm) same
      exact ProgramSetup.decoder_payload_member decoder (index - 13238273) 8 (by decide +kernel)
        payload equal.symm active
    next padding =>
      have tag := congrArg (fun row : List Source.BaseField => row.getLast?.getD 0) same
      simp [ProgramSetup.packTagged] at tag
      exact ((by exact of_decide_eq_true rfl : (46 : Source.BaseField) ≠ 0) tag).elim

/-- The public unrolled factory binds the subword decoder in both cache modes. -/
theorem unrolled_subword_decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (configuration : Configuration)
    (which : configuration = .subwordMemoryUncached ∨ configuration = .subwordMemoryCached)
    (index : Nat) (query : Vector Source.BaseField 9) (bounded : query[0].val < 65536)
    (same : ProgramSetup.packTagged 9 46 (ProgramRows.maskRow (masks .subwordMemory) query) =
      unrolledProgramLookupRows initial columns configuration 0 index) :
    ProgramRows.maskRow (masks .subwordMemory) query ∈ columns .subwordMemory := by
  have widths : ∀ row ∈ columns .subwordMemory, row.length = 8 := by
    intro row member
    exact unrolled_column_width setup .subwordMemoryUncached .subwordMemory _ rfl rfl row member
  have payloadWidth : (ProgramRows.maskRow (masks .subwordMemory) query).length = 8 := by
    rw [unrolled_mask_eq setup .subwordMemory]
    exact unrolled_native_mask_width .subwordMemoryUncached .subwordMemory _ rfl rfl query
  rcases which with rfl | rfl
  all_goals
    apply subword_decoder_member (columns .subwordMemory) (ROM.words initial) index widths _ payloadWidth
    · simpa [unrolledProgramLookupRows, programRows, unrolledDecoderColumns, pooledFamily] using same
    · exact active_decoder_payload (masks .subwordMemory) query bounded

end Airbender.Compiler.NativeProgramSetup
