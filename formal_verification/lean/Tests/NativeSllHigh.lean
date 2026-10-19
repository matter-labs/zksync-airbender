import Airbender.Review.Helpers.Tables.NativeSllHigh

namespace Tests.NativeSllHigh
open Airbender Verification

theorem all_rows (i : Fin 2097152) : NativeSllHigh.data.rowNat i = (sllHighRow i).push 49 :=
  SllHighProofs.native_rows i

theorem actual_extent_offset : NativeSllHigh.data.length = 2097152 ∧
    NativeSllHigh.data.nativeOffset = 2363393 := ⟨rfl,rfl⟩

theorem exact_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    sllHighTable.Contains #[] query ↔ NativeSllHigh.Contains query := native_sll_high_membership query

private theorem at_index (i : Fin 2097152) : NativeSllHigh.Contains ((sllHighRow i).map Nat.cast) :=
  (native_sll_high_membership _).mp ⟨i,rfl⟩

theorem no_shift_last_word : NativeSllHigh.Contains #v[65535,0,65535] := by
  convert at_index ⟨65535,by decide⟩ using 1
  decide +kernel

theorem shift_one : NativeSllHigh.Contains #v[131071,0,65534] := by
  convert at_index ⟨131071,by decide⟩ using 1
  decide +kernel

theorem top_bit_discarded : NativeSllHigh.Contains #v[98304,0,0] := by
  convert at_index ⟨98304,by decide⟩ using 1
  decide +kernel

theorem last_surviving_bit : NativeSllHigh.Contains #v[983041,0,32768] := by
  convert at_index ⟨983041,by decide⟩ using 1
  decide +kernel

theorem next_bit_discarded : NativeSllHigh.Contains #v[983042,0,0] := by
  convert at_index ⟨983042,by decide⟩ using 1
  decide +kernel

theorem shift_sixteen : NativeSllHigh.Contains #v[1114111,0,0] := by
  convert at_index ⟨1114111,by decide⟩ using 1
  decide +kernel

theorem last_row : NativeSllHigh.Contains #v[2097151,0,0] := by
  convert at_index ⟨2097151,by decide⟩ using 1
  decide +kernel

theorem wrong_result_rejected : ¬ NativeSllHigh.Contains #v[131071,0,65535] := by
  intro member
  have result := (native_sll_high_result _ member).2.2.2
  have wrong : (BitVec.ofNat 32 (65535 * 65536)) ≠
      (BitVec.ofNat 32 (65535 * 65536)) <<< 1 := by decide +kernel
  exact wrong result

theorem nonzero_low_rejected : ¬ NativeSllHigh.Contains #v[123,1,123] := by
  intro member
  have result := (native_sll_high_result _ member).2.2.1
  have wrong : (1 : ZMod mersenne31Modulus) ≠ 0 := by decide +kernel
  exact wrong result

theorem oversized_key_rejected : ¬ NativeSllHigh.Contains #v[2097152,0,0] := by
  intro member
  have result := (native_sll_high_result _ member).1
  have canonical : (((2097152 : Nat) : ZMod mersenne31Modulus).val) = 2097152 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by decide)]
  change (((2097152 : Nat) : ZMod mersenne31Modulus).val) < 2097152 at result
  rw [canonical] at result
  exact (Nat.lt_irrefl 2097152) result

end Tests.NativeSllHigh
