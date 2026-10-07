import Airbender.Proofs.Blake2G
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Blake2G.Tables
import Mathlib.Tactic.IntervalCases

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

private def control (_ : Fin 512) : Vector Nat 7 := Vector.replicate 7 0

private def chunkQuery (a b c tag : Nat) : Lookup (ZMod babyBearModulus) where
  table := (Blake2G.setupTable control).toRaw
  entry := #v[.const (a : ZMod babyBearModulus), .const (b : ZMod babyBearModulus),
    .const (c : ZMod babyBearModulus), .const 0, .const 0, .const 0, .const 0,
    .const 0, .const (tag : ZMod babyBearModulus)]

private def emptyEnv : Environment (ZMod babyBearModulus) := Verification.environment (fun _ => 0)

-- A maximum-width boundary pair has a real row in the modeled static setup.
example : (chunkQuery 511 256 255 20).Contains emptyEnv := by
  change ∃ i : Fin 344896,
    ((chunkQuery 511 256 255 20).entry.map (Expression.eval emptyEnv)) =
      (Blake2G.setupRow control i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨82240 + 511 * 512 + 256, by decide⟩, ?_⟩
  have row : Blake2G.setupRow control ⟨82240 + 511 * 512 + 256, by decide⟩ =
      #v[511, 256, 255, 0, 0, 0, 0, 0, 20] := by decide
  rw [row]
  change (Vector.map (Expression.eval emptyEnv)
    (#v[.const (511 : ZMod babyBearModulus), .const 256, .const 255,
      .const 0, .const 0, .const 0, .const 0, .const 0, .const 20] :
      Vector (Expression (ZMod babyBearModulus)) 9)) =
    (#v[511, 256, 255, 0, 0, 0, 0, 0, 20] : Vector Nat 9).map
      (fun (n : Nat) => (n : ZMod babyBearModulus))
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map]
  interval_cases j <;> rfl

-- The first out-of-range input is rejected by table membership itself.
example : ¬ (chunkQuery 512 0 512 20).Contains emptyEnv := by
  intro member
  have result := Blake2G.Proofs.xor_lookup (by decide) 4 member (by simp [Expression.eval])
  have value : (512 : ZMod babyBearModulus).val = 512 := by decide
  have bound : (512 : ZMod babyBearModulus).val < 512 := by
    simpa [Expression.eval] using result.1
  rw [value] at bound
  omega

-- In-range inputs with the wrong XOR cannot be accepted either.
example : ¬ (chunkQuery 7 3 5 4).Contains emptyEnv := by
  intro member
  have result := Blake2G.Proofs.xor_lookup (by decide) 0 member (by simp [Expression.eval])
  have equation : (5 : ZMod babyBearModulus).val =
      (7 : ZMod babyBearModulus).val ^^^ (3 : ZMod babyBearModulus).val := by
    simpa [Expression.eval] using result.2.2.2
  have wrong : ¬ (5 : ZMod babyBearModulus).val =
      (7 : ZMod babyBearModulus).val ^^^ (3 : ZMod babyBearModulus).val := by decide
  exact wrong equation

end Tests.Blake2G
