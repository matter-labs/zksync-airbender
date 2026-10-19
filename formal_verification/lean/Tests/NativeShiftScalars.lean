import Airbender.Review.Helpers.Tables.NativeShiftScalars

namespace Tests.NativeShiftScalars
open Airbender Verification

theorem all_rows (kind : ShiftScalarKind) (i : Fin kind.length) :
    NativeShiftScalars.row kind i = (kind.row i).push kind.tag :=
  ShiftScalarProofs.native_rows kind i

theorem actual_offsets : NativeShiftScalars.dataTruncate.nativeOffset = 200705 ∧
    NativeShiftScalars.dataSignFill.nativeOffset = 8654849 ∧
    NativeShiftScalars.dataRange.nativeOffset = 10752001 := by exact ⟨rfl,rfl,rfl⟩

theorem exact_membership (kind : ShiftScalarKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    kind.table.Contains #[] query ↔ NativeShiftScalars.Contains kind query :=
  native_shift_scalar_membership kind query

private theorem at_index (kind : ShiftScalarKind) (i : Fin kind.length) :
    NativeShiftScalars.Contains kind ((kind.row i).map Nat.cast) :=
  (native_shift_scalar_membership kind _).mp ⟨i,rfl⟩

theorem truncation_last : NativeShiftScalars.Contains .truncate #v[65535,31,0] := by
  convert at_index .truncate ⟨65535,by decide⟩ using 1
  decide +kernel

theorem range_last : NativeShiftScalars.Contains .range #v[65535,0,0] := by
  convert at_index .range ⟨65535,by decide⟩ using 1
  decide +kernel

/-- Negative high limb and shift zero must produce an empty fill mask. -/
theorem sign_shift_zero : NativeShiftScalars.Contains .signFill #v[32768,0,0] := by
  convert at_index .signFill ⟨32768,by decide⟩ using 1
  decide +kernel

theorem sign_shift_one : NativeShiftScalars.Contains .signFill #v[98304,0,32768] := by
  convert at_index .signFill ⟨98304,by decide⟩ using 1
  decide +kernel

theorem sign_shift_sixteen : NativeShiftScalars.Contains .signFill #v[1081344,0,65535] := by
  convert at_index .signFill ⟨1081344,by decide⟩ using 1
  decide +kernel

theorem positive_shift_last : NativeShiftScalars.Contains .signFill #v[2064383,0,0] := by
  convert at_index .signFill ⟨2064383,by decide⟩ using 1
  decide +kernel

theorem sign_shift_last : NativeShiftScalars.Contains .signFill #v[2097151,65534,65535] := by
  convert at_index .signFill ⟨2097151,by decide⟩ using 1
  decide +kernel

theorem bad_truncation_rejected :
    ¬ NativeShiftScalars.Contains .truncate #v[65535,30,0] := by
  intro member
  have result := (native_shift_truncation _ member).2.1
  have wrong : (30 : Nat) ≠ 65535 % 32 := by decide
  exact wrong result

theorem bad_padding_rejected :
    ¬ NativeShiftScalars.Contains .range #v[123,1,0] := by
  intro member
  have result := (native_shift_padded_range _ member).2.1
  have wrong : (1 : ZMod mersenne31Modulus) ≠ 0 := by decide +kernel
  exact wrong result

theorem bad_sign_fill_rejected :
    ¬ NativeShiftScalars.Contains .signFill #v[32768,65535,65535] := by
  intro member
  have result := (native_shift_sign_fill _ member).2.2.2
  have wrong : (BitVec.ofNat 32 (65535 + 65536 * 65535)) ≠
      (BitVec.allOnes 32) <<< 32 := by decide +kernel
  exact wrong result

theorem oversized_shift_key_rejected :
    ¬ NativeShiftScalars.Contains .signFill #v[2097152,0,0] := by
  intro member
  have result := (native_shift_sign_fill _ member).1
  have canonical : (((2097152 : Nat) : ZMod mersenne31Modulus).val) = 2097152 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by decide)]
  change (((2097152 : Nat) : ZMod mersenne31Modulus).val) < 2097152 at result
  rw [canonical] at result
  exact (Nat.lt_irrefl 2097152) result

end Tests.NativeShiftScalars
