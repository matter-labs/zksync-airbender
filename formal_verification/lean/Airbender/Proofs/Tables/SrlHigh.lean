import Airbender.Proofs.Tables.SrlHighPart0
import Airbender.Proofs.Tables.SrlHighPart1
import Airbender.Proofs.Tables.SrlHighPart2
import Airbender.Proofs.Tables.SrlHighPart3
import Airbender.Proofs.Tables.SrlHighPart4
import Airbender.Proofs.Tables.SrlHighColumns
import Airbender.Proofs.Tables.SrlHighMath
import Airbender.Proofs.Tables.BlockTransport
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.SrlHighProofs
open Setup Setup.Proofs NativeSrlHigh
set_option warningAsError true
set_option Elab.async false

theorem prefix_outputs : checkBlocks srlHighLowOutput 0 lowPrefix = true := by
  rw [prefix_parts]
  simp only [checkBlocks_append_iff,List.map_append,List.sum_append,and_assoc,
    part0_extent,part1_extent,part2_extent,part3_extent,Nat.reduceAdd]
  exact ⟨outputs_part0,outputs_part1,outputs_part2,outputs_part3,outputs_part4⟩

theorem reused_suffix_outputs : checkBlocks srlHighLowOutput 1048576
    (SrlLowProofs.part0 ++ SrlLowProofs.part1 ++ SrlLowProofs.part2 ++
      SrlLowProofs.part3 ++ SrlLowProofs.part4) = true := by
  have checked : checkBlocks srlLowOutput 0
      (SrlLowProofs.part0 ++ SrlLowProofs.part1 ++ SrlLowProofs.part2 ++
        SrlLowProofs.part3 ++ SrlLowProofs.part4) = true := by
    simp only [checkBlocks_append_iff,List.map_append,List.sum_append,and_assoc,
      SrlLowProofs.part0_extent,SrlLowProofs.part1_extent,SrlLowProofs.part2_extent,
      SrlLowProofs.part3_extent,Nat.reduceAdd]
    exact ⟨SrlLowProofs.outputs_part0,SrlLowProofs.outputs_part1,
      SrlLowProofs.outputs_part2,SrlLowProofs.outputs_part3,SrlLowProofs.outputs_part4⟩
  apply checkBlocks_transfer srlLowOutput srlHighLowOutput _ 0 1048576 checked
  intro n
  simpa only [Nat.zero_add] using low_after_sixteen n.val

theorem native_low_outputs : checkBlocks srlHighLowOutput 0 data.columns[1].blocks.toList = true := by
  rw [native_low_shape,checkBlocks_append_iff,prefix_extent,Nat.zero_add]
  exact ⟨prefix_outputs,reused_suffix_outputs⟩

theorem native_low (i : Fin 2097152) :
    data.columns[1].get? i.val = some (srlHighLowOutput i.val) := by
  have result := checkBlocks_sound srlHighLowOutput _ 0 i.val native_low_outputs
    (by rw [native_low_extent]; exact i.isLt)
  simpa only [Column.get?,Nat.zero_add] using result

theorem native_rows (i : Fin 2097152) : data.rowNat i = (srlHighRow i).push 51 := by
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat,srlHighRow,native_key,native_low,native_high,native_tag]

theorem native_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    srlHighTable.Contains #[] query ↔ Contains query := by
  change (∃ i : Fin 2097152, query = (srlHighRow i).map Nat.cast) ↔ _
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
        (BitVec.ofNat 32 ((query[0].val % 65536) * 65536)) >>> (query[0].val / 65536) := by
  have clean : ∃ i : Fin 2097152, query = (srlHighRow i).map Nat.cast :=
    (native_membership query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have low := low_bound i.val
  have high := SrlLowProofs.low_bound i.val
  have bits := shifted_bits i.val
  simp [srlHighRow,canonical _ i.isLt,
    canonical _ (by omega : srlHighLowOutput i.val < 2097152),
    canonical _ (by omega : srlLowOutput i.val < 2097152),low,high,bits]

end Airbender.Verification.SrlHighProofs
