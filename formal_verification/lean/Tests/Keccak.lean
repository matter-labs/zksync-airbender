import Airbender.Proofs.Keccak.Claims
import Airbender.Proofs.Keccak.Lookups
import Mathlib.Tactic.IntervalCases

set_option Elab.async false

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
    · apply Trace.Proofs.range_contains
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

theorem oversizedControlRejected {w : Nat → ZMod babyBearModulus}
    (oversized : 2048 ≤ (w 3).val) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints permissiveSetup) := by
  intro holds
  exact Nat.not_lt_of_ge oversized (Keccak.babyBear_local_checks holds).readBound

theorem inactiveZeroTags (i : Fin 40) :
    Keccak.Proofs.byteTag permissiveSetup inactiveRow i = 0 :=
  Keccak.Proofs.inactive_tags (by decide) inactiveSatisfies rfl i

private def control (_ : Fin 4096) : Vector Nat 6 := Vector.replicate 6 0

private def xorQuery (a b c : Nat) : Lookup (ZMod babyBearModulus) where
  table := (Keccak.setupTable control).toRaw
  entry := #v[.const (a : ZMod babyBearModulus), .const (b : ZMod babyBearModulus),
    .const (c : ZMod babyBearModulus), .const 0, .const 0, .const 0, .const 0, .const 4]

private def emptyEnv : Environment (ZMod babyBearModulus) :=
  Verification.environment (fun _ => 0)

-- A real setup row accepts the boundary byte pair; no permissive table is used.
theorem xorBoundaryAccepted : (xorQuery 255 1 254).Contains emptyEnv := by
  change ∃ i : Fin 1249281, (xorQuery 255 1 254).entry.map (Expression.eval emptyEnv) =
    (Keccak.setupRow control i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨65282, by decide⟩, ?_⟩
  have row : Keccak.setupRow control ⟨65282, by decide⟩ = #v[255, 1, 254, 0, 0, 0, 0, 4] := by
    rw [Keccak.Proofs.setup_row_characterization]
    decide
  rw [row]
  change (Vector.map (Expression.eval emptyEnv)
    (#v[.const (255 : ZMod babyBearModulus), .const 1, .const 254,
      .const 0, .const 0, .const 0, .const 0, .const 4] :
      Vector (Expression (ZMod babyBearModulus)) 8)) =
    (#v[255, 1, 254, 0, 0, 0, 0, 4] : Vector Nat 8).map
      (fun (n : Nat) => (n : ZMod babyBearModulus))
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map]
  interval_cases j <;> rfl

-- In-range inputs do not permit a different result.
theorem wrongXorRejected : ¬ (xorQuery 255 1 255).Contains emptyEnv := by
  intro member
  have relation := Keccak.Proofs.xor_lookup (by decide) member (by simp [Expression.eval])
  have equation : (255 : ZMod babyBearModulus).val =
      (255 : ZMod babyBearModulus).val ^^^ (1 : ZMod babyBearModulus).val := by
    simpa [xorQuery, Expression.eval] using relation.2.2.2
  exact (by decide : ¬ (255 : ZMod babyBearModulus).val =
    (255 : ZMod babyBearModulus).val ^^^ (1 : ZMod babyBearModulus).val) equation

-- The first out-of-range byte is rejected without an operand-range premise.
theorem oversizedXorOperandRejected : ¬ (xorQuery 256 0 256).Contains emptyEnv := by
  intro member
  have relation := Keccak.Proofs.xor_lookup (by decide) member (by simp [Expression.eval])
  have bound : (256 : ZMod babyBearModulus).val < 256 := by
    simpa [xorQuery, Expression.eval] using relation.1
  exact (by decide : ¬ (256 : ZMod babyBearModulus).val < 256) bound

end Tests.Keccak
