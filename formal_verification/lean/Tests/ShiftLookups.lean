import Airbender.Review.Circuits.ShiftBinop.Lookups
import Tests.NativeBinary
import Tests.NativeShiftScalars
import Tests.NativeSllLow
import Tests.NativeSllHigh
import Tests.NativeSrlLow
import Tests.NativeSrlHigh

namespace Tests.ShiftLookups
open Airbender Verification ShiftBinop
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private abbrev accepts (query : Vector (ZMod mersenne31Modulus) 4) : Prop :=
  (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] query

theorem actual_zero : accepts #v[0, 0, 0, 0] :=
  (native_lookup_zero #v[0, 0, 0]).mpr rfl

theorem nonzero_inactive_rejected : ¬ accepts #v[1, 0, 0, 0] := by
  intro member
  have impossible := (native_lookup_zero #v[1, 0, 0]).mp member
  have wrong : (#v[1, 0, 0] : Vector (ZMod mersenne31Modulus) 3) ≠ #v[0, 0, 0] := by decide +kernel
  exact wrong impossible

theorem unsupported_selector_rejected : ¬ accepts #v[0, 0, 0, 1] := by
  intro member
  have impossible := native_lookup_selector _ member
  have canonical : (#v[0, 0, 0, 1] : Vector (ZMod mersenne31Modulus) 4)[3].val = 1 := by decide +kernel
  rw [canonical] at impossible
  omega

theorem binary_complementary (kind : BinaryKind) :
    accepts #v[90, 165, kind.apply 90 165, kind.tag] :=
  (native_lookup_binary kind #v[90, 165, kind.apply 90 165]).mpr (Tests.NativeBinary.complementary kind)

theorem binary_oversized_rejected (kind : BinaryKind) :
    ¬ accepts #v[256, 0, 0, kind.tag] := by
  intro member
  exact Tests.NativeBinary.bad_byte_rejected kind ((native_lookup_binary kind _).mp member)

theorem binary_wrong_result_rejected : ¬ accepts #v[90, 165, 254, 4] := by
  intro member
  exact Tests.NativeBinary.bad_result_rejected ((native_lookup_binary .xor _).mp member)

/-- Correct XOR data cannot be accepted under the AND selector. -/
theorem binary_wrong_selector_rejected : ¬ accepts #v[90, 165, 255, 7] := by
  intro member
  have result := (native_binary_result .and _ ((native_lookup_binary .and #v[90, 165, 255]).mp member)).2.2.2
  have wrong : (255 : BitVec 8) ≠ byteOperation BinaryKind.and.tag 90 165 := by decide +kernel
  exact wrong result

/-- The accepted selector bound concerns its canonical field value. -/
theorem canonical_field_selector : accepts #v[90, 165, 255, ((mersenne31Modulus + 4 : Nat) : ZMod mersenne31Modulus)] := by
  have tag : ((mersenne31Modulus + 4 : Nat) : ZMod mersenne31Modulus) = 4 := by
    simp
  rw [tag]
  exact binary_complementary .xor

theorem truncation_last : accepts #v[65535, 31, 0, 47] :=
  (native_lookup_scalar .truncate #v[65535, 31, 0]).mpr Tests.NativeShiftScalars.truncation_last

theorem range_last : accepts #v[65535, 0, 0, 53] :=
  (native_lookup_scalar .range #v[65535, 0, 0]).mpr Tests.NativeShiftScalars.range_last

theorem negative_shift_zero : accepts #v[32768, 0, 0, 52] :=
  (native_lookup_scalar .signFill #v[32768, 0, 0]).mpr Tests.NativeShiftScalars.sign_shift_zero

theorem sll_low_last : accepts #v[2097151, 0, 32768, 48] :=
  (native_lookup_sll_low #v[2097151, 0, 32768]).mpr Tests.NativeSllLow.last_row

theorem sll_high_last : accepts #v[2097151, 0, 0, 49] :=
  (native_lookup_sll_high #v[2097151, 0, 0]).mpr Tests.NativeSllHigh.last_row

theorem srl_low_last : accepts #v[2097151, 0, 0, 50] :=
  (native_lookup_srl_low #v[2097151, 0, 0]).mpr Tests.NativeSrlLow.last_row

theorem srl_high_last : accepts #v[2097151, 1, 0, 51] :=
  (native_lookup_srl_high #v[2097151, 1, 0]).mpr Tests.NativeSrlHigh.last_row

theorem bad_truncation_rejected : ¬ accepts #v[65535, 30, 0, 47] := by
  intro member
  exact Tests.NativeShiftScalars.bad_truncation_rejected ((native_lookup_scalar .truncate _).mp member)

theorem bad_padding_rejected : ¬ accepts #v[123, 1, 0, 53] := by
  intro member
  exact Tests.NativeShiftScalars.bad_padding_rejected ((native_lookup_scalar .range _).mp member)

theorem bad_sign_fill_rejected : ¬ accepts #v[32768, 65535, 65535, 52] := by
  intro member
  exact Tests.NativeShiftScalars.bad_sign_fill_rejected ((native_lookup_scalar .signFill _).mp member)

theorem sll_low_bad_result_rejected : ¬ accepts #v[131071, 65534, 0, 48] := by
  intro member
  exact Tests.NativeSllLow.wrong_high_rejected ((native_lookup_sll_low _).mp member)

theorem sll_high_bad_result_rejected : ¬ accepts #v[131071, 0, 65535, 49] := by
  intro member
  exact Tests.NativeSllHigh.wrong_result_rejected ((native_lookup_sll_high _).mp member)

theorem srl_low_bad_result_rejected : ¬ accepts #v[131071, 32768, 0, 50] := by
  intro member
  exact Tests.NativeSrlLow.wrong_result_rejected ((native_lookup_srl_low _).mp member)

theorem srl_high_bad_result_rejected : ¬ accepts #v[131071, 32768, 32768, 51] := by
  intro member
  exact Tests.NativeSrlHigh.wrong_high_rejected ((native_lookup_srl_high _).mp member)

/-- A row valid in SLL-high cannot substitute for the low-input SLL result. -/
theorem crossed_sll_region_rejected : ¬ accepts #v[2097151, 0, 0, 48] := by
  intro member
  have result := (native_sll_low_result _ ((native_lookup_sll_low #v[2097151, 0, 0]).mp member)).2.2.2
  have wrong : BitVec.ofNat 32 (0 + 0 * 65536) ≠
      (BitVec.ofNat 32 (2097151 % 65536)) <<< (2097151 / 65536) := by decide +kernel
  exact wrong result

end Tests.ShiftLookups
