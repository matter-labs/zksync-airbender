import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.BabyBear
import Mathlib.Tactic.LinearCombination

namespace Airbender.SerializedInverse

/-- The common serialized residue fixes the characteristic. No capacity bound
is needed: the existing prime-divisor argument excludes every other prime. -/
theorem scale64_field {p : Nat} [Fact p.Prime]
    (compatible : Scale64 p) : p = babyBearModulus := by
  apply babyBear_eq_of_natCast_zero
  change 64 * (-31457280 : ZMod p) = 1 at compatible
  unfold babyBearModulus
  linear_combination -compatible

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem clock_scale64 {p : Nat} (compatible : Clock p) : Scale64 p := by
  change (-3840 : ZMod p) * 524288 = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem clock_field {p : Nat} [Fact p.Prime]
    (compatible : Clock p) : p = babyBearModulus :=
  scale64_field (clock_scale64 compatible)

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem limb16_scale64 {p : Nat} (compatible : Limb16 p) : Scale64 p := by
  change (-30720 : ZMod p) * 65536 = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem limb16_field {p : Nat} [Fact p.Prime]
    (compatible : Limb16 p) : p = babyBearModulus :=
  scale64_field (limb16_scale64 compatible)

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem scale32_scale64 {p : Nat} (compatible : Scale32 p) : Scale64 p := by
  change 32 * (-62914560 : ZMod p) = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem scale32_field {p : Nat} [Fact p.Prime]
    (compatible : Scale32 p) : p = babyBearModulus :=
  scale64_field (scale32_scale64 compatible)

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem scale128_scale64 {p : Nat} (compatible : Scale128 p) : Scale64 p := by
  change 128 * (-15728640 : ZMod p) = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem scale128_field {p : Nat} [Fact p.Prime]
    (compatible : Scale128 p) : p = babyBearModulus :=
  scale64_field (scale128_scale64 compatible)

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem scale256_scale64 {p : Nat} (compatible : Scale256 p) : Scale64 p := by
  change 256 * (-7864320 : ZMod p) = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem scale256_field {p : Nat} [Fact p.Prime]
    (compatible : Scale256 p) : p = babyBearModulus :=
  scale64_field (scale256_scale64 compatible)

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem scale512_scale64 {p : Nat} (compatible : Scale512 p) : Scale64 p := by
  change 512 * (-3932160 : ZMod p) = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem scale512_field {p : Nat} [Fact p.Prime]
    (compatible : Scale512 p) : p = babyBearModulus :=
  scale64_field (scale512_scale64 compatible)

/-- Convert an exact imported coefficient equation to the common residue. -/
theorem scale4096_scale64 {p : Nat} (compatible : Scale4096 p) : Scale64 p := by
  change 4096 * (-491520 : ZMod p) = 1 at compatible
  change 64 * (-31457280 : ZMod p) = 1
  linear_combination compatible

/-- This fixed imported coefficient already requires BabyBear under primality. -/
theorem scale4096_field {p : Nat} [Fact p.Prime]
    (compatible : Scale4096 p) : p = babyBearModulus :=
  scale64_field (scale4096_scale64 compatible)

/-- Compatibility conversion retained for the existing BLAKE byte binding. -/
theorem scale64_scale256 {p : Nat} (compatible : Scale64 p) : Scale256 p := by
  change 64 * (-31457280 : ZMod p) = 1 at compatible
  change 256 * (-7864320 : ZMod p) = 1
  linear_combination compatible

end Airbender.SerializedInverse
