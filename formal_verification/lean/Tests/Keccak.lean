import Airbender.Review.Keccak.Theorems

namespace Tests.Keccak
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

-- A deliberately permissive fixed setup isolates the structural guarantees.
-- These tests do not establish the semantics of the XOR/ANDN/rotation tables.
def permissiveSetup : Table (ZMod babyBearModulus) (fields 8) where
  name := "StructuralTestsOnly"
  Contains _ _ := True

def inactiveRow (v : Nat) : ZMod babyBearModulus :=
  if v = 86 then 8192 else if v = 87 then 24640 else
  if v = 88 then 41088 else if v = 89 then 57536 else 0

theorem inactiveSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment inactiveRow)
      (Keccak.importedConstraints permissiveSetup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · simp only [Keccak.importedConstraints, FlatOperation.lookups,
      List.forall_mem_cons]
    constructor
    · apply Verification.range16_contains
      decide
    · simp [Lookup.Contains, permissiveSetup, Table.toRaw]

theorem inactiveChecks : Keccak.LocalChecks inactiveRow :=
  Keccak.babyBear_local_checks inactiveSatisfies

theorem unalignedPointerRejected {w : Nat → ZMod babyBearModulus}
    (pointer : w 13 = 1) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints permissiveSetup) := by
  intro holds
  have alignment := (Keccak.babyBear_local_checks holds).pointerAlignment
  rw [pointer] at alignment
  exact (by decide : (1 : ZMod babyBearModulus).val % 256 ≠ 0) alignment

theorem multipleModesRejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (first : w 63 = 1) (second : w 64 = 1) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints permissiveSetup) := by
  intro holds
  have counts := (Keccak.babyBear_local_checks holds).modeCount
  have two : (w 63).val + (w 64).val ≤
      ∑ i : Fin 7, (w Keccak.Variables.modeColumns[i]).val := by
    simp [Keccak.Variables.modeColumns, Fin.sum_univ_succ]
  rw [counts, active, first, second] at two
  have one : (1 : ZMod babyBearModulus).val = 1 := by decide
  rw [one] at two
  omega

end Tests.Keccak
