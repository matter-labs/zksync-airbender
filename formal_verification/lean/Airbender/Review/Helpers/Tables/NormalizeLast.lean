import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Airbender.Verification
/-- Native zero-constant normalization replaces only the reserved final row.
    This is a finite-field source reference, not Rust/u64/FFT refinement. -/
def normalizeLast {R : Type} [AddCommGroup R] (size : Nat) (rows : Nat → R) (i : Nat) : R :=
  if i = size-1 then -(∑ j ∈ Finset.range (size-1), rows j) else rows i

def normalizeRows {R : Type} [AddCommGroup R] {width : Nat}
    (size : Nat) (rows : Nat → Vector R width) (i : Nat) : Vector R width :=
  Vector.ofFn fun column => normalizeLast size (fun j => (rows j)[column.val]) i
end Airbender.Verification
