import Slop.Keccak.Claims
import Mathlib.Tactic.IntervalCases
import Slop.BabyBear

namespace Tests.KeccakTheta
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

-- A supplied controller row makes the local arithmetic test independent of
-- the still-open controller schedule and global memory argument.
def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]

abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control

def row (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 66 ∨ v = 70 then 1
  else if v = 3 then 3 else if v = 5 then 11
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if 15 ≤ v ∧ v < 63 then
    let lane := (v - 15) / 8
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let shared : Nat := if limb = 0 then 1 else if limb = 3 then 256 else 0
    ((if lane = 5 then shared
    else if (v - 15) % 4 < 2 then 65535 else 65535 ^^^ shared : Nat) : ZMod babyBearModulus)
  else if v = 86 then 8192 else if v = 87 then 24640
  else if v = 88 then 41088 else if v = 89 then 57536
  else if 102 ≤ v ∧ v < 222 then
    let col := ((v - 102) % 24) / 8
    let byte := (v - 102) % 8
    let shared : Nat := if byte = 0 ∨ byte = 7 then 1 else 0
    ((if col = 0 then 255 else if col = 1 then shared else 255 ^^^ shared : Nat) : ZMod babyBearModulus)
  else 0

private theorem bytesHold (i : Fin 40) :
    (Keccak.Proofs.byteQuery setup i).Contains (Verification.environment row) := by
  rw [Keccak.Proofs.byte_query_shape]
  change ∃ index : Fin 1249281,
    (Keccak.Proofs.byteEntry setup i).map (Expression.eval (Verification.environment row)) =
      (Keccak.setupRow control index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨65281 + if i.val % 8 = 0 ∨ i.val % 8 = 7 then 1 else 0,
    by split_ifs <;> omega⟩, ?_⟩
  fin_cases i <;>
    dsimp [Keccak.Proofs.byteEntry, Keccak.Proofs.byteQuery, Keccak.importedConstraints,
      FlatOperation.lookups]
  all_goals norm_num [Expression.eval, Verification.environment, row, Keccak.setupRow, Keccak.byteRow]
  all_goals decide +kernel

private theorem controllerHolds :
    ((FlatOperation.lookups (Keccak.importedConstraints setup)).get
      ⟨1, by rw [Keccak.lookup_count]; decide⟩).Contains (Verification.environment row) := by
  change ∃ index : Fin 1249281,
    ((FlatOperation.lookups (Keccak.importedConstraints setup))[1]).entry.map
      (Expression.eval (Verification.environment row)) =
    (Keccak.setupRow control index).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨67588, by decide⟩, ?_⟩
  have physicalRow : Keccak.setupRow control ⟨67588, by decide⟩ =
      #v[2051, 0, 5, 10, 15, 20, 25, 37] := by decide
  rw [physicalRow]
  change (Vector.map (n := 8) (Expression.eval (Verification.environment row))
    ((FlatOperation.lookups (Keccak.importedConstraints setup))[1]).entry) =
      (#v[2051, 0, 5, 10, 15, 20, 25, 37] : Vector Nat 8).map
        (fun (n : Nat) => (n : ZMod babyBearModulus))
  dsimp [Keccak.importedConstraints, FlatOperation.lookups]
  apply Vector.ext
  intro j hj
  interval_cases j <;> decide +kernel +revert

theorem satisfies : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraints setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    by_cases range : i = 0
    · subst i
      apply Verification.range16_contains
      decide
    by_cases controller : i = 1
    · subst i
      simpa only [List.get_eq_getElem] using controllerHolds
    have relation := bytesHold ⟨i - 2, by omega⟩
    have index : i - 2 + 2 = i := by omega
    simpa only [Keccak.Proofs.byteQuery, List.get_eq_getElem, Fin.val_mk, index] using relation

-- These values are read from the native ports after proving the full row holds.
theorem nativeLaneValues : Keccak.readLane row 0 = 18446744073709551615 ∧
    Keccak.readLane row 5 = 72057594037927937 ∧
    Keccak.writeLane row 0 = 18374686479671623678 := by decide

theorem wrongWriteRejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (theta : w 66 = 1)
    (source : Keccak.readLane w 0 = 18446744073709551615)
    (scratch : Keccak.readLane w 5 = 72057594037927937)
    (wrong : Keccak.writeLane w 0 = 18374686479671623679) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints setup) := by
  intro holds
  have equation := (Keccak.Proofs.theta_lane_xor (by decide) holds active theta (0 : Fin 5)).2.2.2
  change Keccak.writeLane w (0 : Fin 6) =
    Keccak.readLane w (0 : Fin 6) ^^^ Keccak.readLane w (5 : Fin 6) at equation
  rw [source, scratch, wrong] at equation
  exact (by decide : ¬ 18374686479671623679 = 18446744073709551615 ^^^ 72057594037927937) equation

theorem referenceColumn : Keccak.ThetaResult (Vector.replicate 25 18446744073709551615)
    (Vector.replicate 5 72057594037927937) (0 : Fin 5) row := by
  apply Keccak.theta_column_soundness (by decide) satisfies
  constructor
  · rfl
  · rfl
  · intro i
    fin_cases i <;> decide
  · decide

private theorem controllerBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31 := by
  intro key
  change ∀ i : Fin 6, (#v[0, 5, 10, 15, 20, 25] : Vector Nat 6)[i] < 31
  decide

theorem nativeFixedRelations : Keccak.ByteLookupChecks control row :=
  Keccak.fixed_lookup_checks (by decide) satisfies

theorem nativeAddresses : Keccak.AddressChecks row :=
  Keccak.address_checks (by decide) (by decide) controllerBounded (by constructor <;> decide) satisfies

-- At the last aligned low-limb block, even the largest modeled lane index
-- and its high word remain below the limb boundary.
theorem boundaryNoCarry : 65280 + 8 * 30 + 4 < Arithmetic.limbBase := by decide

end Tests.KeccakTheta
