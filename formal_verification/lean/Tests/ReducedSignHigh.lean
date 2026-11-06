import Airbender.Review.Circuits.ReducedMachine.Tables.SignHigh

namespace Tests.ReducedSignHigh
open Airbender Airbender.ReducedMachine SignHigh

private theorem at_index (n : Nat) (bound : n < 65536) :
    Contains ((#v[n,n / 32768,n / 256,16]).map (Nat.cast : Nat → ZMod mersenne31Modulus)) := by
  refine ⟨⟨n,bound⟩,?_⟩
  rw [Setup.TableData.row,SignHighProofs.rows]

theorem actual_geometry : data.length = 65536 ∧ data.nativeOffset = 196609 := ⟨rfl,rfl⟩

theorem first : Contains #v[0,0,0,16] := by
  convert at_index 0 (by decide) using 1; decide +kernel

theorem byte_end : Contains #v[255,0,0,16] := by
  convert at_index 255 (by decide) using 1; decide +kernel

theorem next_byte : Contains #v[256,0,1,16] := by
  convert at_index 256 (by decide) using 1; decide +kernel

theorem positive_end : Contains #v[32767,0,127,16] := by
  convert at_index 32767 (by decide) using 1; decide +kernel

theorem negative_start : Contains #v[32768,1,128,16] := by
  convert at_index 32768 (by decide) using 1; decide +kernel

theorem last : Contains #v[65535,1,255,16] := by
  convert at_index 65535 (by decide) using 1; decide +kernel

theorem bad_sign_rejected : ¬ Contains #v[32768,0,128,16] := by
  intro member
  have result := (native_sign_high _ member).2.1
  exact (by decide +kernel : ¬ (0 : ZMod mersenne31Modulus).val =
    (32768 : ZMod mersenne31Modulus).val / 32768) result

theorem bad_high_rejected : ¬ Contains #v[65535,1,254,16] := by
  intro member
  have result := (native_sign_high _ member).2.2.1
  exact (by decide +kernel : ¬ (254 : ZMod mersenne31Modulus).val =
    (65535 : ZMod mersenne31Modulus).val / 256) result

theorem bad_tag_rejected : ¬ Contains #v[65535,1,255,17] := by
  intro member
  have result := (native_sign_high _ member).2.2.2
  exact (by decide +kernel : (17 : ZMod mersenne31Modulus) ≠ 16) result

theorem oversized_key_rejected : ¬ Contains #v[65536,0,0,16] := by
  intro member
  have result := (native_sign_high _ member).1
  exact (by decide +kernel : ¬ (65536 : ZMod mersenne31Modulus).val < 65536) result

end Tests.ReducedSignHigh
