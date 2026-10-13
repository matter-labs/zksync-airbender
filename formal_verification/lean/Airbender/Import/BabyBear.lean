import Airbender.Import.Json
import Airbender.Review.Helpers.Core.Field

namespace Airbender
open Lean

/-- Canonical residues, ready for algebraic semantics (no Mathlib dependency). -/
abbrev Fp := Fin babyBearModulus

def Fp.ofNat (n : Nat) : Fp := ⟨n % babyBearModulus, Nat.mod_lt _ (by decide)⟩
def Fp.zero : Fp := Fp.ofNat 0
def Fp.one : Fp := Fp.ofNat 1
def Fp.add (a b : Fp) : Fp := Fp.ofNat (a.val + b.val)
def Fp.mul (a b : Fp) : Fp := Fp.ofNat (a.val * b.val)

/-- Serialized `BabyBearField.0` is a Montgomery residue, not a canonical residue.
    Preserve the source representation for exact JSON round trips. -/
structure Coefficient where
  raw : BoundedNat babyBearModulus
  deriving Repr

instance : FromJson Coefficient where
  fromJson? j := Coefficient.mk <$> fromJson? j

instance : ToJson Coefficient where
  toJson c := toJson c.raw

/-- Inverse of R = 2^32 modulo the BabyBear prime. See field/src/baby_bear/base.rs. -/
def montgomeryInverse : Nat := 943718400

def Coefficient.canonical (c : Coefficient) : Fp :=
  Fp.ofNat (c.raw.val * montgomeryInverse)

theorem montgomery_inverse_correct :
    ((2 ^ 32 % babyBearModulus) * montgomeryInverse) % babyBearModulus = 1 := by decide

theorem serialized_one_correct :
    (Coefficient.mk ⟨268435454, by decide⟩).canonical = Fp.one := by decide

theorem serialized_neg_one_correct :
    (Coefficient.mk ⟨1744830467, by decide⟩).canonical.val = babyBearModulus - 1 := by decide

end Airbender
