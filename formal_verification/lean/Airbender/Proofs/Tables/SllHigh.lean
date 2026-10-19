import Airbender.Proofs.Tables.SllHighPart0
import Airbender.Proofs.Tables.SllHighPart1
import Airbender.Proofs.Tables.SllHighPart2
import Airbender.Proofs.Tables.SllHighPart3
import Airbender.Proofs.Tables.SllHighPart4
import Airbender.Proofs.Tables.SllHighPart5
import Airbender.Proofs.Tables.SllHighColumns
import Airbender.Proofs.Tables.SllHighMath
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
set_option warningAsError true
set_option Elab.async false

theorem native_outputs : checkBlocks sllHighOutput 0 data.columns[2].blocks.toList = true := by
  rw [parts]
  simp only [checkBlocks_append_iff,List.map_append,List.sum_append,and_assoc,part0_extent,part1_extent,part2_extent,
    part3_extent,part4_extent,Nat.reduceAdd]
  exact ⟨outputs_part0,outputs_part1,outputs_part2,outputs_part3,outputs_part4,outputs_part5⟩

theorem native_output (i : Fin 2097152) :
    data.columns[2].get? i.val = some (sllHighOutput i.val) := by
  have result := checkBlocks_sound sllHighOutput _ 0 i.val native_outputs
    (by rw [native_output_extent]; exact i.isLt)
  simpa only [Column.get?,Nat.zero_add] using result

theorem native_rows (i : Fin 2097152) : data.rowNat i = (sllHighRow i).push 49 := by
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat,sllHighRow,native_key,native_output,native_zero,native_tag]

theorem native_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    sllHighTable.Contains #[] query ↔ Contains query := by
  change (∃ i : Fin 2097152, query = (sllHighRow i).map Nat.cast) ↔ _
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
    query[0].val < 2097152 ∧ query[2].val < 65536 ∧ query[1] = 0 ∧
      BitVec.ofNat 32 (query[2].val * 65536) =
        (BitVec.ofNat 32 ((query[0].val % 65536) * 65536)) <<< (query[0].val / 65536) := by
  have clean : ∃ i : Fin 2097152, query = (sllHighRow i).map Nat.cast :=
    (native_membership query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have bound := high_bound i.val
  have bits := high_bits i.val
  simp [sllHighRow,canonical _ i.isLt,
    canonical _ (by omega : sllHighOutput i.val < 2097152),bound,bits]

end Airbender.Verification.SllHighProofs
