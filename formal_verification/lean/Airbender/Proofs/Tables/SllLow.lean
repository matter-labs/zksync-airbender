import Airbender.Proofs.Tables.SllLowPart0
import Airbender.Proofs.Tables.SllLowPart1
import Airbender.Proofs.Tables.SllLowPart2
import Airbender.Proofs.Tables.SllLowPart3
import Airbender.Proofs.Tables.SllLowPart4
import Airbender.Proofs.Tables.SllLowPart5
import Airbender.Proofs.Tables.SllLowColumns
import Airbender.Proofs.Tables.SllLowMath
import Airbender.Proofs.Tables.BlockTransport
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.SllLowProofs
open Setup Setup.Proofs NativeSllLow
set_option warningAsError true
set_option Elab.async false

theorem prefix_outputs : checkBlocks sllLowHighOutput 0 highPrefix = true := by
  rw [prefix_parts]
  simp only [checkBlocks_append_iff,List.map_append,List.sum_append,and_assoc,
    part0_extent,part1_extent,part2_extent,part3_extent,part4_extent,Nat.reduceAdd]
  exact ⟨outputs_part0,outputs_part1,outputs_part2,outputs_part3,outputs_part4,outputs_part5⟩

theorem reused_suffix_outputs : checkBlocks sllLowHighOutput 1048576
    (SllHighProofs.part0 ++ SllHighProofs.part1 ++ SllHighProofs.part2 ++
      SllHighProofs.part3 ++ SllHighProofs.part4) = true := by
  have checked : checkBlocks sllHighOutput 0
      (SllHighProofs.part0 ++ SllHighProofs.part1 ++ SllHighProofs.part2 ++
        SllHighProofs.part3 ++ SllHighProofs.part4) = true := by
    simp only [checkBlocks_append_iff,List.map_append,List.sum_append,and_assoc,
      SllHighProofs.part0_extent,SllHighProofs.part1_extent,SllHighProofs.part2_extent,
      SllHighProofs.part3_extent,Nat.reduceAdd]
    exact ⟨SllHighProofs.outputs_part0,SllHighProofs.outputs_part1,
      SllHighProofs.outputs_part2,SllHighProofs.outputs_part3,SllHighProofs.outputs_part4⟩
  apply checkBlocks_transfer sllHighOutput sllLowHighOutput _ 0 1048576 checked
  intro n
  simpa only [Nat.zero_add] using high_after_sixteen n.val

theorem native_high_outputs : checkBlocks sllLowHighOutput 0 data.columns[2].blocks.toList = true := by
  rw [native_high_shape,checkBlocks_append_iff,prefix_extent,Nat.zero_add]
  exact ⟨prefix_outputs,reused_suffix_outputs⟩

theorem native_high (i : Fin 2097152) :
    data.columns[2].get? i.val = some (sllLowHighOutput i.val) := by
  have result := checkBlocks_sound sllLowHighOutput _ 0 i.val native_high_outputs
    (by rw [native_high_extent]; exact i.isLt)
  simpa only [Column.get?,Nat.zero_add] using result

theorem native_rows (i : Fin 2097152) : data.rowNat i = (sllLowRow i).push 48 := by
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat,sllLowRow,native_key,native_low,native_high,native_tag]

theorem native_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    sllLowTable.Contains #[] query ↔ Contains query := by
  change (∃ i : Fin 2097152, query = (sllLowRow i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,by simp [TableData.row,native_rows,Vector.map_push]⟩
  · rintro ⟨i,same⟩
    refine ⟨i,?_⟩
    ext lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row,native_rows,Vector.map_push,Vector.getElem_push,bound] using selected

private theorem canonical (n : Nat) (bound : n < 2097152) :
    (n : ZMod mersenne31Modulus).val = n := by
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by change n < 2147483647; omega)]

theorem native_result (query : Vector (ZMod mersenne31Modulus) 3) (member : Contains query) :
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2].val < 65536 ∧
      BitVec.ofNat 32 (query[1].val + query[2].val * 65536) =
        (BitVec.ofNat 32 (query[0].val % 65536)) <<< (query[0].val / 65536) := by
  have clean : ∃ i : Fin 2097152, query = (sllLowRow i).map Nat.cast :=
    (native_membership query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have low := SllHighProofs.high_bound i.val
  have high := high_bound i.val
  have bits := shifted_bits i.val
  simp [sllLowRow,canonical _ i.isLt,
    canonical _ (by omega : sllHighOutput i.val < 2097152),
    canonical _ (by omega : sllLowHighOutput i.val < 2097152),low,high,bits]

end Airbender.Verification.SllLowProofs
