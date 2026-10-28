import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Tables.DecoderPrefix
import Airbender.Proofs.Tables.SelectedDecoderProgram
import Airbender.Data.Decoder.Setup.Unified

namespace Airbender.Trace.NativeDecoder.Proofs.Unified
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem prefix_checked : fixedTags unifiedSetup.prefixTags.blocks.toList = true := by
  decide +kernel

private def paddingValues : Vector Nat unifiedSetup.width :=
  Vector.ofFn fun lane => (unifiedSetup.padding.columns[lane].get? 0).getD 0

private theorem padding_checked (lane : Fin unifiedSetup.width) :
    constantTail paddingValues[lane] 0 unifiedSetup.padding.columns[lane].blocks.toList = true := by
  fin_cases lane <;> decide +kernel

private theorem padding_extent (lane : Fin unifiedSetup.width) :
    (unifiedSetup.padding.columns[lane].blocks.toList.map Block.length).sum = unifiedSetup.padding.length := by
  fin_cases lane <;> decide +kernel

/-- Every real row is checked against original Sail decoding of the independently
    imported text; unsupported slots retain the actual native sentinel. -/
theorem real_rows (index : Fin 4) :
    if (unifiedEntry index).data.family = .machine then
      unifiedSetup.row ⟨index.val, by exact Nat.lt_of_lt_of_le index.isLt (by decide +kernel)⟩ =
        queryNat (unifiedEntry index)
    else (unifiedSetup.row ⟨index.val, by exact Nat.lt_of_lt_of_le index.isLt (by decide +kernel)⟩)[0] =
      babyBearModulus - 1 := by
  fin_cases index <;> decide +kernel

private theorem small_query (index : Fin 4) (lane : Fin 10) :
    (queryNat (unifiedEntry index))[lane] ≤ babyBearModulus / 2 := by
  fin_cases index <;> fin_cases lane <;> decide +kernel

private theorem unsupported_checked :
    constantTail (babyBearModulus - 1) 4 unifiedSetup.realRows.columns[0].blocks.toList = true := by
  decide +kernel

private theorem real_extent :
    (unifiedSetup.realRows.columns[0].blocks.toList.map Block.length).sum = unifiedSetup.realRows.length := by
  decide +kernel

private theorem unsupported_row (index : Fin unifiedSetup.realRows.length) (outside : 4 ≤ index.val) :
    (unifiedSetup.row ⟨index.val, by have := index.isLt; omega⟩)[0] = babyBearModulus - 1 := by
  have actual := constantTail_sound _ _ _ unsupported_checked index.val outside
    (by rw [real_extent]; exact index.isLt)
  unfold PackedSetup.row
  simp only [if_pos index.isLt]
  rw [normalize_first unifiedSetup (by decide +kernel) (by decide +kernel)]
  simp only [Vector.getElem_map]
  rw [show unifiedSetup.realRows.offset = 0 by rfl, Nat.zero_add]
  change (unifiedSetup.realRows.columns[0].get? index.val).getD 0 = babyBearModulus - 1
  exact congrArg (fun value => value.getD 0) actual

/-- The actual setup supplies the former table-content contract. Public typed
    PC encoding and lookup authentication retain their distinct boundaries. -/
theorem lookup_sound [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536) (query : Vector (ZMod p) 9)
    (typed : query[0].val < 65536)
    (holds : unifiedSetup.lookup query) :
    (decoderTable unifiedProgram .machine).Contains #[] query := by
  have selected := lookup_to_slice unifiedSetup query
    (fun n => fixedTags_ne_decoder hp _ prefix_checked n) holds
  apply decoder_member hp unifiedSetup unifiedProgram .machine ?_ ?_ query typed selected
  · intro index
    by_cases leading : index.val < 4
    · let n : Fin 4 := ⟨index.val, leading⟩
      have actual := real_rows n
      by_cases family : (unifiedEntry n).data.family = .machine
      · rw [if_pos family] at actual
        left
        refine ⟨unifiedEntry n, unified_program_member n, family, ?_⟩
        rw [actual]
        exact signed_queryNat _ (small_query n)
      · rw [if_neg family] at actual
        right
        rw [actual]
        exact signed_filler
    · right
      rw [unsupported_row index (by omega)]
      exact signed_filler
  · intro index outside
    have actual := padding_row unifiedSetup paddingValues padding_checked padding_extent (by rfl) index outside
    rw [actual]
    right
    change (signedValue 0 : ZMod p) = 0
    norm_num [signedValue, babyBearModulus]

end Airbender.Trace.NativeDecoder.Proofs.Unified
