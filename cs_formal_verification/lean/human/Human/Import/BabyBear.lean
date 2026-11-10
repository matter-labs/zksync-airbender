module
public import Human.Import.Json
public import Human.Helpers.Core.Field

@[expose] public section

namespace Airbender

/-- Canonical residues, ready for algebraic semantics (no Mathlib dependency). -/
abbrev Fp := Fin babyBearModulus

def Fp.ofNat (n : Nat) : Fp := ⟨n % babyBearModulus, Nat.mod_lt _ (by decide)⟩
def Fp.one : Fp := Fp.ofNat 1

/-- Serialized `BabyBearField.0` is a Montgomery residue, not a canonical residue.
    Preserve the source representation for exact JSON round trips. -/
structure Coefficient where
  raw : BoundedNat babyBearModulus
  deriving Repr

def Coefficient.canonical (c : Coefficient) : Fp :=
  Fp.ofNat (c.raw.val * montgomeryInverse)

theorem montgomery_inverse_correct :
    ((2 ^ 32 % babyBearModulus) * montgomeryInverse) % babyBearModulus = 1 := by decide

theorem serialized_one_correct :
    (Coefficient.mk ⟨268435454, by decide⟩).canonical = Fp.one := by decide

theorem serialized_neg_one_correct :
    (Coefficient.mk ⟨1744830467, by decide⟩).canonical.val = babyBearModulus - 1 := by decide

end Airbender
