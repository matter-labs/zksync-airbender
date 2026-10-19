import Airbender.Proofs.Tables.SrlLowPart0
import Airbender.Proofs.Tables.SrlLowPart1
import Airbender.Proofs.Tables.SrlLowPart2
import Airbender.Proofs.Tables.SrlLowPart3
import Airbender.Proofs.Tables.SrlLowPart4
import Airbender.Proofs.Tables.SrlLowPart5
import Airbender.Proofs.Tables.SrlLowColumns
import Airbender.Proofs.Tables.SrlLowMath
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.SrlLowProofs
open Setup Setup.Proofs NativeSrlLow
set_option warningAsError true
set_option Elab.async false

theorem native_outputs : checkBlocks srlLowOutput 0 data.columns[1].blocks.toList = true := by
  rw [parts]
  simp only [checkBlocks_append_iff,List.map_append,List.sum_append,and_assoc,part0_extent,part1_extent,part2_extent,
    part3_extent,part4_extent,Nat.reduceAdd]
  exact ⟨outputs_part0,outputs_part1,outputs_part2,outputs_part3,outputs_part4,outputs_part5⟩

theorem native_output (i : Fin 2097152) :
    data.columns[1].get? i.val = some (srlLowOutput i.val) := by
  have result := checkBlocks_sound srlLowOutput _ 0 i.val native_outputs
    (by rw [native_output_extent]; exact i.isLt)
  simpa only [Column.get?,Nat.zero_add] using result

theorem native_rows (i : Fin 2097152) : data.rowNat i = (srlLowRow i).push 50 := by
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat,srlLowRow,native_key,native_output,native_zero,native_tag]

theorem native_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    srlLowTable.Contains #[] query ↔ Contains query := by
  change (∃ i : Fin 2097152, query = (srlLowRow i).map Nat.cast) ↔ _
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
    query[0].val < 2097152 ∧ query[1].val < 65536 ∧ query[2] = 0 ∧
      BitVec.ofNat 32 query[1].val =
        (BitVec.ofNat 32 (query[0].val % 65536)) >>> (query[0].val / 65536) := by
  have clean : ∃ i : Fin 2097152, query = (srlLowRow i).map Nat.cast :=
    (native_membership query).mpr member
  obtain ⟨i,rfl⟩ := clean
  have bound := low_bound i.val
  have bits := low_bits i.val
  simp [srlLowRow,canonical _ i.isLt,
    canonical _ (by omega : srlLowOutput i.val < 2097152),bound,bits]

end Airbender.Verification.SrlLowProofs
