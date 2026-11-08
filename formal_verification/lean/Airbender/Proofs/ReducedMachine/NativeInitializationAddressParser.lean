import Airbender.Review.Circuits.ReducedMachine.InitializationWindow
import Airbender.Proofs.ReducedMachine.NativeInitializationBoundary

namespace Airbender.NativeInitializationAddressParserProofs
open Airbender.NativeInitializationWindow Airbender.NativeInitializationBoundary Airbender.NativeInitializationOrdering
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Abstract bounded-mask proof BEFORE any native domain or public fixture. -/
theorem high_mask {value : Nat} (bound : value < 65536) : value &&& 4294901760 = 0 := by
  have low : value &&& 65535 = value := Nat.and_two_pow_sub_one_of_lt_two_pow (n := 16) bound
  calc
    value &&& 4294901760 = (value &&& 65535) &&& 4294901760 := by rw [low]
    _ = value &&& (65535 &&& 4294901760) := Nat.and_assoc _ _ _
    _ = 0 := by rw [show 65535 &&& 4294901760 = 0 by decide +kernel,Nat.and_zero]

theorem packed {low high : Nat} (lo : low < 65536) (hi : high < 65536) :
    ((BitVec.ofNat 32 low) ||| ((BitVec.ofNat 32 high) <<< 16)).toNat = low+65536*high := by
  have low32 : low < 2^32 := by omega
  have high32 : high < 2^32 := by omega
  have shifted : high <<< 16 < 2^32 := by rw [Nat.shiftLeft_eq]; omega
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.mod_eq_of_lt low32,
    Nat.mod_eq_of_lt high32,Nat.mod_eq_of_lt shifted]
  rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt (i := 16) lo high,Nat.shiftLeft_eq]
  omega

theorem parsed {values : Vector F 6} (bounds : values[0].val < 65536 ∧ values[1].val < 65536) :
    parseAddress values = some (BitVec.ofNat 32 (addressValue values)) := by
  have mask {value : Nat} (bound : value < 65536) :
      (BitVec.ofNat 32 value) &&& 0xffff0000 = (0 : BitVec 32) := by
    apply BitVec.eq_of_toNat_eq
    have b32 : value < 2^32 := by omega
    change (value % 2^32) &&& 4294901760 = 0
    rw [Nat.mod_eq_of_lt b32]
    exact high_mask bound
  unfold parseAddress
  rw [if_pos ⟨mask bounds.1,mask bounds.2⟩]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have word : addressValue values < 2^32 := by unfold addressValue; omega
  rw [packed bounds.1 bounds.2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt word]
  rfl

theorem parsed_value {values : Vector F 6} (bounds : values[0].val < 65536 ∧ values[1].val < 65536) :
    (BitVec.ofNat 32 (addressValue values)).toNat = addressValue values := by
  have word : addressValue values < 2^32 := by unfold addressValue; omega
  exact Nat.mod_eq_of_lt word

end Airbender.NativeInitializationAddressParserProofs
