import Mathlib.Data.ZMod.Basic

/-!
# Compatibility with imported inverse coefficients

Each predicate names one exact equation already used by the native bindings;
operand order and coefficients are retained. Every displayed radix times its
negative coefficient is `-2013265920`, so the equation implies that the
characteristic divides the BabyBear prime `2013265921`. Under primality, each
condition therefore forces that field, independently of all capacity bounds.
`Airbender.Proofs.SerializedInverse` checks this once through the existing
prime-divisor argument and supplies the family conversions.

These are compatibility conditions for fixed imported data, not generic inverse
parameters. Arithmetic lemmas such as `value_of_scaled_chunks` keep a variable
`inverse` with `(radix : ZMod p) * inverse = 1` and remain genuinely generic.
A different native field needs its own exported coefficients and checked binding.
-/

namespace Airbender.SerializedInverse

/-- Imported inverse of the 19-bit native clock radix. -/
abbrev Clock (p : Nat) : Prop := (-3840 : ZMod p) * 524288 = 1

/-- Imported inverse of the 16-bit limb radix, also used for PC/address carries. -/
abbrev Limb16 (p : Nat) : Prop := (-30720 : ZMod p) * 65536 = 1

/-- Imported coefficient for 32-byte alignment. -/
abbrev Scale32 (p : Nat) : Prop := 32 * (-62914560 : ZMod p) = 1

/-- Imported coefficient for 64-byte alignment and hash chunk decompositions. -/
abbrev Scale64 (p : Nat) : Prop := 64 * (-31457280 : ZMod p) = 1

/-- Imported inverse for a 7-bit chunk. -/
abbrev Scale128 (p : Nat) : Prop := 128 * (-15728640 : ZMod p) = 1

/-- Imported inverse for a byte. -/
abbrev Scale256 (p : Nat) : Prop := 256 * (-7864320 : ZMod p) = 1

/-- Imported inverse for a 9-bit chunk, including local writeback conversions. -/
abbrev Scale512 (p : Nat) : Prop := 512 * (-3932160 : ZMod p) = 1

/-- Imported inverse for a 12-bit chunk in the BLAKE mixing decomposition. -/
abbrev Scale4096 (p : Nat) : Prop := 4096 * (-491520 : ZMod p) = 1

end Airbender.SerializedInverse
