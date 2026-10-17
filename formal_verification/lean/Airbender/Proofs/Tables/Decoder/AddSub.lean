import Airbender.Proofs.Tables.DecoderPrefix
import Airbender.Proofs.Tables.SelectedDecoderProgram
import Airbender.Review.Helpers.Decoder.SetupData.AddSub

namespace Airbender.Trace.NativeDecoder.Proofs.AddSub
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem prefix_checked : fixedTags addSubSetup.prefixTags.blocks.toList = true := by
  decide +kernel

private def paddingValues : Vector Nat addSubSetup.width :=
  Vector.ofFn fun lane => if lane.val = 0 then babyBearModulus - 1 else 0

private theorem padding_checked (lane : Fin addSubSetup.width) :
    constantTail paddingValues[lane] 0 addSubSetup.padding.columns[lane].blocks.toList = true := by
  fin_cases lane <;> decide +kernel

private theorem padding_extent (lane : Fin addSubSetup.width) :
    (addSubSetup.padding.columns[lane].blocks.toList.map Block.length).sum = addSubSetup.padding.length := by
  fin_cases lane <;> decide +kernel

/-- Every real row is checked against original Sail decoding of the independently
    imported text; unsupported slots retain the actual native sentinel. -/
theorem real_rows (index : Fin 4) :
    if (pooledEntry index).data.family = .addSub then
      addSubSetup.row ⟨index.val, by exact Nat.lt_of_lt_of_le index.isLt (by decide +kernel)⟩ =
        queryNat (pooledEntry index)
    else (addSubSetup.row ⟨index.val, by exact Nat.lt_of_lt_of_le index.isLt (by decide +kernel)⟩)[0] =
      babyBearModulus - 1 := by
  fin_cases index <;> decide +kernel

private theorem small_query (index : Fin 4) (lane : Fin 10) :
    (queryNat (pooledEntry index))[lane] ≤ babyBearModulus / 2 := by
  fin_cases index <;> fin_cases lane <;> decide +kernel

private theorem unsupported_checked :
    constantTail (babyBearModulus - 1) 4 addSubSetup.realRows.columns[0].blocks.toList = true := by
  decide +kernel

private theorem real_extent :
    (addSubSetup.realRows.columns[0].blocks.toList.map Block.length).sum = addSubSetup.realRows.length := by
  decide +kernel

private theorem unsupported_row (index : Fin addSubSetup.realRows.length) (outside : 4 ≤ index.val) :
    (addSubSetup.row ⟨index.val, by have := index.isLt; omega⟩)[0] = babyBearModulus - 1 := by
  have actual := constantTail_sound _ _ _ unsupported_checked index.val outside
    (by rw [real_extent]; exact index.isLt)
  unfold PackedSetup.row
  simp only [if_pos index.isLt]
  rw [normalize_first addSubSetup (by decide +kernel) (by decide +kernel)]
  simp only [Vector.getElem_map]
  rw [show addSubSetup.realRows.offset = 0 by rfl, Nat.zero_add]
  change (addSubSetup.realRows.columns[0].get? index.val).getD 0 = babyBearModulus - 1
  exact congrArg (fun value => value.getD 0) actual

/-- The actual setup supplies the former table-content contract. Public typed
    PC encoding and lookup authentication retain their distinct boundaries. -/
theorem lookup_sound [Fact p.Prime] (hp : 65536 < p) (query : Vector (ZMod p) 9)
    (typed : query[0].val < 65536)
    (holds : addSubSetup.lookup query) :
    (decoderTable pooledProgram .addSub).Contains #[] query := by
  have selected := lookup_to_slice addSubSetup query
    (fun n => fixedTags_ne_decoder hp _ prefix_checked n) holds
  apply decoder_member hp addSubSetup pooledProgram .addSub ?_ ?_ query typed selected
  · intro index
    by_cases leading : index.val < 4
    · let n : Fin 4 := ⟨index.val, leading⟩
      have actual := real_rows n
      by_cases family : (pooledEntry n).data.family = .addSub
      · rw [if_pos family] at actual
        left
        refine ⟨pooledEntry n, pooled_program_member n, family, ?_⟩
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
    have actual := padding_row addSubSetup paddingValues padding_checked padding_extent (by rfl) index outside
    rw [actual]
    left
    change (signedValue (babyBearModulus - 1) : ZMod p) = -1
    exact signed_filler

end Airbender.Trace.NativeDecoder.Proofs.AddSub
