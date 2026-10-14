/-
# What the Rust functions in rust/src/main.rs should compute (u32 = BitVec 32, arithmetic mod 2^32).
-/
namespace Spec

def inc (x : BitVec 32) : BitVec 32 := x + 1
def double (x : BitVec 32) : BitVec 32 := 2 * x
/-- `3x + 1`: what the program leaves in `a0`. -/
def combine (x : BitVec 32) : BitVec 32 := 3 * x + 1

/-- The coefficients of the polynomial evaluated by `poly_eval` (Rust `COEFFS`): `cᵢ = 31 i² + 7`.
(The field and the polynomial itself are in `SpecPoly.lean`.) -/
def coeffNat (i : Nat) : Nat := 31 * i ^ 2 + 7

end Spec
