import Slop.Keccak.FixedTables
import Slop.BabyBear
import Mathlib.Tactic.IntervalCases

namespace Tests.KeccakFixedTables
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

private def control (_ : Fin 4096) : Vector Nat 6 := Vector.replicate 6 0
private def emptyEnv : Environment (ZMod babyBearModulus) := Verification.environment (fun _ => 0)
private def query (tag a b c : Nat) : Lookup (ZMod babyBearModulus) :=
  Lookup.mk (Keccak.setupTable control).toRaw
    #v[.const (a : ZMod babyBearModulus), .const (b : ZMod babyBearModulus),
      .const (c : ZMod babyBearModulus), .const 0, .const 0, .const 0, .const 0,
      .const (tag : ZMod babyBearModulus)]

private theorem accepted (tag a b c : Nat) (index : Fin 1249281)
    (physicalRow : Keccak.setupRow control index = #v[a, b, c, 0, 0, 0, 0, tag]) :
    (query tag a b c).Contains emptyEnv := by
  change ∃ index : Fin 1249281, (query tag a b c).entry.map (Expression.eval emptyEnv) =
    (Keccak.setupRow control index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨index, ?_⟩
  rw [physicalRow]
  change (Vector.map (n := 8) (Expression.eval emptyEnv)
    (#v[.const (a : ZMod babyBearModulus), .const (b : ZMod babyBearModulus), .const (c : ZMod babyBearModulus),
      .const 0, .const 0, .const 0, .const 0, .const (tag : ZMod babyBearModulus)] :
      Vector (Expression (ZMod babyBearModulus)) 8)) =
    (#v[a, b, c, 0, 0, 0, 0, tag] : Vector Nat 8).map
      (fun (n : Nat) => (n : ZMod babyBearModulus))
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map]
  interval_cases j <;> rfl

-- Round zero is identity; round 24 includes the final constant's high byte.
theorem iotaInitialAccepted : (query 38 255 0 255).Contains emptyEnv :=
  accepted _ _ _ _ ⟨69888, by decide⟩ (by decide)

theorem iotaFinalByteAccepted : (query 38 255 248 127).Contains emptyEnv :=
  accepted _ _ _ _ ⟨133376, by decide⟩ (by decide)

theorem andnAccepted : (query 39 170 255 85).Contains emptyEnv :=
  accepted _ _ _ _ ⟨200619, by decide⟩ (by decide)

theorem maximumRotationAccepted : (query 40 1048575 32767 32768).Contains emptyEnv :=
  accepted _ _ _ _ ⟨1249280, by decide⟩ (by decide)

theorem zeroRotationAccepted : (query 40 65535 0 65535).Contains emptyEnv :=
  accepted _ _ _ _ ⟨266240, by decide⟩ (by decide)

private theorem rejected (tag a b c : Nat) (tagBound : tag < babyBearModulus)
    (notController : tag ≠ 37) (aBound : a < babyBearModulus)
    (bBound : b < babyBearModulus) (cBound : c < babyBearModulus)
    (wrong : ¬ Keccak.ByteOperationFacts tag a b c) :
    ¬ (query tag a b c).Contains emptyEnv := by
  intro member
  have tagValue : (tag : ZMod babyBearModulus).val = tag := ZMod.val_natCast_of_lt tagBound
  have facts := Keccak.Proofs.fixed_lookup (by decide) member
    (by change (tag : ZMod babyBearModulus).val ≠ 37; rw [tagValue]; exact notController)
  change Keccak.ByteOperationFacts (tag : ZMod babyBearModulus).val
    (a : ZMod babyBearModulus).val (b : ZMod babyBearModulus).val
    (c : ZMod babyBearModulus).val at facts
  rw [tagValue, ZMod.val_natCast_of_lt aBound, ZMod.val_natCast_of_lt bBound,
    ZMod.val_natCast_of_lt cBound] at facts
  exact wrong facts

theorem wrongIotaRejected : ¬ (query 38 255 248 255).Contains emptyEnv :=
  rejected _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold Keccak.ByteOperationFacts; decide)

theorem wrongAndnRejected : ¬ (query 39 170 255 170).Contains emptyEnv :=
  rejected _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold Keccak.ByteOperationFacts; decide)

theorem wrongRotationRejected : ¬ (query 40 1048575 32768 32767).Contains emptyEnv :=
  rejected _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold Keccak.ByteOperationFacts; decide)

theorem oversizedRotationRejected : ¬ (query 40 1048576 0 0).Contains emptyEnv :=
  rejected _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold Keccak.ByteOperationFacts; decide)

theorem nonzeroPaddingRejected : ¬ (query 0 1 0 0).Contains emptyEnv :=
  rejected _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by unfold Keccak.ByteOperationFacts; decide)

end Tests.KeccakFixedTables
