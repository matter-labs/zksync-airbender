import Airbender.Proofs.Tables.DecoderPrefix
import Airbender.Proofs.Tables.SelectedDecoderProgram
import Airbender.Review.Helpers.Decoder.SetupData.JumpBranch

namespace Airbender.Trace.NativeDecoder.Proofs.JumpBranch
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem prefix_checked : fixedTags jumpBranchSetup.prefixTags.blocks.toList = true := by
  decide +kernel

private def paddingValues : Vector Nat jumpBranchSetup.width :=
  Vector.ofFn fun lane => (jumpBranchSetup.padding.columns[lane].get? 0).getD 0

private theorem padding_checked (lane : Fin jumpBranchSetup.width) :
    constantTail paddingValues[lane] 0 jumpBranchSetup.padding.columns[lane].blocks.toList = true := by
  fin_cases lane <;> decide +kernel

private theorem padding_extent (lane : Fin jumpBranchSetup.width) :
    (jumpBranchSetup.padding.columns[lane].blocks.toList.map Block.length).sum = jumpBranchSetup.padding.length := by
  fin_cases lane <;> decide +kernel

/-- Every real row is checked against original Sail decoding of the independently
    imported text; unsupported slots retain the actual native sentinel. -/
theorem real_rows (index : Fin 4) :
    if (pooledEntry index).data.family = .jumpBranchSlt then
      jumpBranchSetup.row ⟨index.val, by exact Nat.lt_of_lt_of_le index.isLt (by decide +kernel)⟩ =
        queryNat (pooledEntry index)
    else (jumpBranchSetup.row ⟨index.val, by exact Nat.lt_of_lt_of_le index.isLt (by decide +kernel)⟩)[0] =
      babyBearModulus - 1 := by
  fin_cases index <;> decide +kernel

private theorem small_query (index : Fin 4) (lane : Fin 10) :
    (queryNat (pooledEntry index))[lane] ≤ babyBearModulus / 2 := by
  fin_cases index <;> fin_cases lane <;> decide +kernel

private theorem unsupported_checked :
    constantTail (babyBearModulus - 1) 4 jumpBranchSetup.realRows.columns[0].blocks.toList = true := by
  decide +kernel

private theorem real_extent :
    (jumpBranchSetup.realRows.columns[0].blocks.toList.map Block.length).sum = jumpBranchSetup.realRows.length := by
  decide +kernel

private theorem unsupported_row (index : Fin jumpBranchSetup.realRows.length) (outside : 4 ≤ index.val) :
    (jumpBranchSetup.row ⟨index.val, by have := index.isLt; omega⟩)[0] = babyBearModulus - 1 := by
  have actual := constantTail_sound _ _ _ unsupported_checked index.val outside
    (by rw [real_extent]; exact index.isLt)
  unfold PackedSetup.row
  simp only [if_pos index.isLt]
  rw [normalize_first jumpBranchSetup (by decide +kernel) (by decide +kernel)]
  simp only [Vector.getElem_map]
  rw [show jumpBranchSetup.realRows.offset = 0 by rfl, Nat.zero_add]
  change (jumpBranchSetup.realRows.columns[0].get? index.val).getD 0 = babyBearModulus - 1
  exact congrArg (fun value => value.getD 0) actual

/-- The actual setup supplies the former table-content contract. Public typed
    PC encoding and lookup authentication retain their distinct boundaries. -/
theorem lookup_sound [Fact p.Prime] (hp : 65536 < p) (query : Vector (ZMod p) 9)
    (typed : query[0].val < 65536)
    (holds : jumpBranchSetup.lookup query) :
    (decoderTable pooledProgram .jumpBranchSlt).Contains #[] query := by
  have selected := lookup_to_slice jumpBranchSetup query
    (fun n => fixedTags_ne_decoder hp _ prefix_checked n) holds
  apply decoder_member hp jumpBranchSetup pooledProgram .jumpBranchSlt ?_ ?_ query typed selected
  · intro index
    by_cases leading : index.val < 4
    · let n : Fin 4 := ⟨index.val, leading⟩
      have actual := real_rows n
      by_cases family : (pooledEntry n).data.family = .jumpBranchSlt
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
    have actual := padding_row jumpBranchSetup paddingValues padding_checked padding_extent (by rfl) index outside
    rw [actual]
    right
    change (signedValue 0 : ZMod p) = 0
    norm_num [signedValue, babyBearModulus]

end Airbender.Trace.NativeDecoder.Proofs.JumpBranch
