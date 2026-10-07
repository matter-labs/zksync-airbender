import Airbender.Proofs.Blake2G
import Airbender.Proofs.BabyBear

namespace Tests.Blake2G
open Airbender

-- This remains impossible regardless of the externally supplied setup contents.
example {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (unaligned : w 13 = 1) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints setup) := by
  intro holds
  have aligned := Blake2G.Proofs.pointer_alignment (by decide) (by decide) holds
  rw [unaligned] at aligned
  have value : (1 : ZMod babyBearModulus).val = 1 := by decide
  rw [value] at aligned
  norm_num at aligned

example {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (nonzero : w 4 ≠ 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints setup) := by
  intro holds
  exact nonzero (Blake2G.Proofs.control_high_zero holds).1

end Tests.Blake2G
