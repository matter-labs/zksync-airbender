import Airbender.Review.Helpers.Tables.NativeSllLow

namespace Tests.NativeSllLow
open Airbender Verification

theorem all_rows (i : Fin 2097152) : NativeSllLow.data.rowNat i = (sllLowRow i).push 48 :=
  SllLowProofs.native_rows i

theorem actual_extent_offset : NativeSllLow.data.length = 2097152 ∧
    NativeSllLow.data.nativeOffset = 266241 := ⟨rfl,rfl⟩

theorem exact_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    sllLowTable.Contains #[] query ↔ NativeSllLow.Contains query := native_sll_low_membership query

private theorem at_index (i : Fin 2097152) : NativeSllLow.Contains ((sllLowRow i).map Nat.cast) :=
  (native_sll_low_membership _).mp ⟨i,rfl⟩

theorem no_shift_last_word : NativeSllLow.Contains #v[65535,65535,0] := by
  convert at_index ⟨65535,by decide⟩ using 1
  decide +kernel

theorem shift_one : NativeSllLow.Contains #v[131071,65534,1] := by
  convert at_index ⟨131071,by decide⟩ using 1
  decide +kernel

theorem first_carry : NativeSllLow.Contains #v[98304,0,1] := by
  convert at_index ⟨98304,by decide⟩ using 1
  decide +kernel

theorem last_without_carry : NativeSllLow.Contains #v[98303,65534,0] := by
  convert at_index ⟨98303,by decide⟩ using 1
  decide +kernel

theorem shift_fifteen : NativeSllLow.Contains #v[1048575,32768,32767] := by
  convert at_index ⟨1048575,by decide⟩ using 1
  decide +kernel

theorem shift_sixteen : NativeSllLow.Contains #v[1114111,0,65535] := by
  convert at_index ⟨1114111,by decide⟩ using 1
  decide +kernel

theorem last_surviving_bit : NativeSllLow.Contains #v[2031617,0,32768] := by
  convert at_index ⟨2031617,by decide⟩ using 1
  decide +kernel

theorem next_bit_discarded : NativeSllLow.Contains #v[2031618,0,0] := by
  convert at_index ⟨2031618,by decide⟩ using 1
  decide +kernel

theorem last_row : NativeSllLow.Contains #v[2097151,0,32768] := by
  convert at_index ⟨2097151,by decide⟩ using 1
  decide +kernel

theorem wrong_low_rejected : ¬ NativeSllLow.Contains #v[131071,65535,1] := by
  intro member
  have result := (native_sll_low_result _ member).2.2.2
  have wrong : BitVec.ofNat 32 (65535 + 1 * 65536) ≠
      (BitVec.ofNat 32 65535) <<< 1 := by decide +kernel
  exact wrong result

theorem wrong_high_rejected : ¬ NativeSllLow.Contains #v[131071,65534,0] := by
  intro member
  have result := (native_sll_low_result _ member).2.2.2
  have wrong : BitVec.ofNat 32 (65534 + 0 * 65536) ≠
      (BitVec.ofNat 32 65535) <<< 1 := by decide +kernel
  exact wrong result

theorem oversized_limb_rejected : ¬ NativeSllLow.Contains #v[131071,65536,1] := by
  intro member
  have result := (native_sll_low_result _ member).2.2.2
  have wrong : BitVec.ofNat 32 (65536 + 1 * 65536) ≠
      (BitVec.ofNat 32 65535) <<< 1 := by decide +kernel
  exact wrong result

theorem oversized_key_rejected : ¬ NativeSllLow.Contains #v[2097152,0,0] := by
  intro member
  have result := (native_sll_low_result _ member).1
  have canonical : (((2097152 : Nat) : ZMod mersenne31Modulus).val) = 2097152 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by decide)]
  change (((2097152 : Nat) : ZMod mersenne31Modulus).val) < 2097152 at result
  rw [canonical] at result
  exact (Nat.lt_irrefl 2097152) result

end Tests.NativeSllLow
