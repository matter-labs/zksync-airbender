module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Core.Proth120

@[expose] public section
namespace Airbender

/-- The host field of a compiled circuit. The radix describes serialized coefficients;
    the size and two-adicity justify the limb and clock arithmetic used by the circuits. -/
class CircuitField (p : Nat) extends Fact p.Prime where
  radixBits : Nat
  montgomeryInverse : Nat
  radix_inverse : (2 ^ radixBits * montgomeryInverse) % p = 1
  limbCapacity : 2 ^ 30 < p
  twoAdicity : 2 ^ 19 ∣ p - 1

namespace CircuitField

instance babyBear : CircuitField babyBearModulus where
  out := babyBearPrime.out
  radixBits := 32
  montgomeryInverse := Airbender.montgomeryInverse
  radix_inverse := by decide +kernel
  limbCapacity := by decide
  twoAdicity := by decide

instance proth120 : CircuitField proth120Modulus where
  out := proth120Prime.out
  radixBits := 128
  montgomeryInverse := 254422546068206553797994320131784704
  radix_inverse := by decide +kernel
  limbCapacity := by decide
  twoAdicity := by decide

/-- The positive representative of minus the inverse of 2^k when 2^k divides p−1. -/
def negInvPow (p k : Nat) : Nat := (p - 1) / 2 ^ k

/-- Interpret a serialized Montgomery residue in its host field. -/
abbrev decode (p : Nat) [CircuitField p] (raw : Nat) : ZMod p :=
  (raw : ZMod p) * (montgomeryInverse p : ZMod p)

abbrev canonical (p : Nat) [CircuitField p] (raw : Nat) : Nat := raw * montgomeryInverse p % p

abbrev signedScalar (p : Nat) [CircuitField p] (raw : Nat) : Int :=
  let n := canonical p raw
  if n ≤ p / 2 then n else (n : Int) - p

end CircuitField
end Airbender
