import Airbender.Review.Helpers.Tables.NativeSrlLow

namespace Tests.NativeSrlLow
open Airbender Verification

theorem all_rows (i : Fin 2097152) : NativeSrlLow.data.rowNat i = (srlLowRow i).push 50 :=
  SrlLowProofs.native_rows i

theorem actual_extent_offset : NativeSrlLow.data.length = 2097152 ∧
    NativeSrlLow.data.nativeOffset = 4460545 := ⟨rfl,rfl⟩

theorem exact_membership (query : Vector (ZMod mersenne31Modulus) 3) :
    srlLowTable.Contains #[] query ↔ NativeSrlLow.Contains query := native_srl_low_membership query

private theorem at_index (i : Fin 2097152) : NativeSrlLow.Contains ((srlLowRow i).map Nat.cast) :=
  (native_srl_low_membership _).mp ⟨i,rfl⟩

theorem no_shift_last_word : NativeSrlLow.Contains #v[65535,65535,0] := by
  convert at_index ⟨65535,by decide⟩ using 1
  decide +kernel

theorem shift_one : NativeSrlLow.Contains #v[131071,32767,0] := by
  convert at_index ⟨131071,by decide⟩ using 1
  decide +kernel

theorem last_surviving_bit : NativeSrlLow.Contains #v[1048575,1,0] := by
  convert at_index ⟨1048575,by decide⟩ using 1
  decide +kernel

theorem below_last_bit : NativeSrlLow.Contains #v[1015807,0,0] := by
  convert at_index ⟨1015807,by decide⟩ using 1
  decide +kernel

theorem shift_sixteen : NativeSrlLow.Contains #v[1114111,0,0] := by
  convert at_index ⟨1114111,by decide⟩ using 1
  decide +kernel

theorem last_row : NativeSrlLow.Contains #v[2097151,0,0] := by
  convert at_index ⟨2097151,by decide⟩ using 1
  decide +kernel

theorem wrong_result_rejected : ¬ NativeSrlLow.Contains #v[131071,32768,0] := by
  intro member
  have result := (native_srl_low_result _ member).2.2.2
  have wrong : (BitVec.ofNat 32 32768) ≠ (BitVec.ofNat 32 65535) >>> 1 := by decide +kernel
  exact wrong result

theorem nonzero_high_rejected : ¬ NativeSrlLow.Contains #v[123,123,1] := by
  intro member
  have result := (native_srl_low_result _ member).2.2.1
  have wrong : (1 : ZMod mersenne31Modulus) ≠ 0 := by decide +kernel
  exact wrong result

theorem oversized_key_rejected : ¬ NativeSrlLow.Contains #v[2097152,0,0] := by
  intro member
  have result := (native_srl_low_result _ member).1
  have canonical : (((2097152 : Nat) : ZMod mersenne31Modulus).val) = 2097152 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by decide)]
  change (((2097152 : Nat) : ZMod mersenne31Modulus).val) < 2097152 at result
  rw [canonical] at result
  exact (Nat.lt_irrefl 2097152) result

end Tests.NativeSrlLow
