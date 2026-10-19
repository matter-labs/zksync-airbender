import Airbender.Review.Helpers.Tables.NativeSrlHigh

namespace Tests.NativeSrlHigh
open Airbender Verification

theorem all_rows (i : Fin 2097152) : NativeSrlHigh.data.rowNat i = (srlHighRow i).push 51 :=
  SrlHighProofs.native_rows i

theorem actual_extent_offset : NativeSrlHigh.data.length = 2097152 ∧
    NativeSrlHigh.data.nativeOffset = 6557697 := ⟨rfl,rfl⟩

theorem exact_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    srlHighTable.Contains #[] query ↔ NativeSrlHigh.Contains query := native_srl_high_membership query

private theorem at_index (i : Fin 2097152) : NativeSrlHigh.Contains ((srlHighRow i).map Nat.cast) :=
  (native_srl_high_membership _).mp ⟨i,rfl⟩

theorem no_shift_last_word : NativeSrlHigh.Contains #v[65535,0,65535] := by
  convert at_index ⟨65535,by decide⟩ using 1
  decide +kernel

theorem first_rotated_row : NativeSrlHigh.Contains #v[65537,32768,0] := by
  convert at_index ⟨65537,by decide⟩ using 1
  decide +kernel

theorem shift_one_last_word : NativeSrlHigh.Contains #v[131071,32768,32767] := by
  convert at_index ⟨131071,by decide⟩ using 1
  decide +kernel

theorem next_shift_zero : NativeSrlHigh.Contains #v[131072,0,0] := by
  convert at_index ⟨131072,by decide⟩ using 1
  decide +kernel

theorem rotated_template_end : NativeSrlHigh.Contains #v[131075,49152,0] := by
  convert at_index ⟨131075,by decide⟩ using 1
  decide +kernel

theorem shift_eleven_first_word : NativeSrlHigh.Contains #v[720897,32,0] := by
  convert at_index ⟨720897,by decide⟩ using 1
  decide +kernel

theorem last_partial_affine_word : NativeSrlHigh.Contains #v[722943,65504,0] := by
  convert at_index ⟨722943,by decide⟩ using 1
  decide +kernel

theorem next_affine_reset : NativeSrlHigh.Contains #v[722944,0,1] := by
  convert at_index ⟨722944,by decide⟩ using 1
  decide +kernel

theorem shift_fifteen : NativeSrlHigh.Contains #v[1048575,65534,1] := by
  convert at_index ⟨1048575,by decide⟩ using 1
  decide +kernel

theorem shift_sixteen : NativeSrlHigh.Contains #v[1114111,65535,0] := by
  convert at_index ⟨1114111,by decide⟩ using 1
  decide +kernel

theorem last_row : NativeSrlHigh.Contains #v[2097151,1,0] := by
  convert at_index ⟨2097151,by decide⟩ using 1
  decide +kernel

theorem below_last_bit : NativeSrlHigh.Contains #v[2064383,0,0] := by
  convert at_index ⟨2064383,by decide⟩ using 1
  decide +kernel

theorem first_last_bit : NativeSrlHigh.Contains #v[2064384,1,0] := by
  convert at_index ⟨2064384,by decide⟩ using 1
  decide +kernel

theorem wrong_low_rejected : ¬ NativeSrlHigh.Contains #v[131071,32767,32767] := by
  intro member
  have result := (native_srl_high_result _ member).2.2.2
  have wrong : BitVec.ofNat 32 (32767 + 32767 * 65536) ≠
      (BitVec.ofNat 32 (65535 * 65536)) >>> 1 := by decide +kernel
  exact wrong result

theorem wrong_high_rejected : ¬ NativeSrlHigh.Contains #v[131071,32768,32768] := by
  intro member
  have result := (native_srl_high_result _ member).2.2.2
  have wrong : BitVec.ofNat 32 (32768 + 32768 * 65536) ≠
      (BitVec.ofNat 32 (65535 * 65536)) >>> 1 := by decide +kernel
  exact wrong result

theorem oversized_limb_rejected : ¬ NativeSrlHigh.Contains #v[65537,65536,0] := by
  intro member
  have result := (native_srl_high_result _ member).2.2.2
  have wrong : BitVec.ofNat 32 (65536 + 0 * 65536) ≠
      (BitVec.ofNat 32 (1 * 65536)) >>> 1 := by decide +kernel
  exact wrong result

theorem oversized_key_rejected : ¬ NativeSrlHigh.Contains #v[2097152,0,0] := by
  intro member
  have result := (native_srl_high_result _ member).1
  have canonical : (((2097152 : Nat) : ZMod mersenne31Modulus).val) = 2097152 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by decide)]
  change (((2097152 : Nat) : ZMod mersenne31Modulus).val) < 2097152 at result
  rw [canonical] at result
  exact (Nat.lt_irrefl 2097152) result

end Tests.NativeSrlHigh
