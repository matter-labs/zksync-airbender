import Tests.Keccak
import Tests.KeccakTheta

set_option Elab.async false

namespace Tests.KeccakControlUpdate
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- These rows isolate the controller equations using the existing permissive
-- fixed setup. The native range query and all 187 equations are still checked.
private def zeroLaneRow (s : Keccak.ControlState) (active : Bool)
    (v : Nat) : ZMod babyBearModulus :=
  let controlRound := if active ∧ s.iteration.val = 0 then s.round.val else 0
  let input := (if active then s.mode.val + 8 * s.iteration.val else 0) + 64 * s.round.val
  let output := if active then s.nextPacked else input
  if v = 0 then (if active then 1 else 0)
  else if v = 3 then (input : Nat) else if v = 5 then (output : Nat)
  else if active ∧ (v = 63 + s.mode.val ∨ v = 70 + s.iteration.val) then 1
  else if 75 ≤ v ∧ v < 80 then ((s.round.val / 2 ^ (v - 75)) % 2 : Nat)
  else if v = 85 then (controlRound : Nat)
  else if 86 ≤ v ∧ v < 90 then (257 * controlRound + 8192 + 16448 * (v - 86) : Nat)
  else 0

private def thetaEnd : Keccak.ControlState := ⟨3, 4, 24⟩
private def chiEnd : Keccak.ControlState := ⟨6, 4, 31⟩

private theorem fixedMembership (w : Nat → ZMod babyBearModulus)
    (zeroPointer : w 13 = 0) :
    ∀ query ∈ FlatOperation.lookups (Keccak.importedConstraints Tests.Keccak.permissiveSetup),
      query.Contains (Verification.environment w) := by
  simp only [Keccak.importedConstraints, FlatOperation.lookups, List.forall_mem_cons]
  constructor
  · apply Verification.range16_contains
    simp [Expression.eval, Verification.environment, zeroPointer, Arithmetic.limbBase]
  · simp [Lookup.Contains, Tests.Keccak.permissiveSetup, Table.toRaw]

theorem thetaRolloverSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (zeroLaneRow thetaEnd true))
      (Keccak.importedConstraints Tests.Keccak.permissiveSetup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  exact ⟨by decide, fixedMembership _ rfl⟩

-- The five local round bits permit 31. This boundary test does not claim that
-- the Keccak protocol schedule allows this row.
theorem chiRolloverSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (zeroLaneRow chiEnd true))
      (Keccak.importedConstraints Tests.Keccak.permissiveSetup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  exact ⟨by decide, fixedMembership _ rfl⟩

theorem inactivePreservesSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (zeroLaneRow chiEnd false))
      (Keccak.importedConstraints Tests.Keccak.permissiveSetup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  exact ⟨by decide, fixedMembership _ rfl⟩

theorem nativeRolloverValues :
    (zeroLaneRow thetaEnd true 3).val = 1571 ∧ (zeroLaneRow thetaEnd true 5).val = 1540 ∧
    (zeroLaneRow chiEnd true 3).val = 2022 ∧ (zeroLaneRow chiEnd true 5).val = 2048 := by decide

theorem nativeControlUpdate : Keccak.ControlUpdateChecks Tests.KeccakTheta.row :=
  Keccak.control_updates (by decide) Tests.KeccakTheta.satisfies

-- A changed control write is rejected using only the native read and the full
-- imported relation; no mode, iteration or round is supplied as a premise.
theorem wrongControlWriteRejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (input : w 3 = 1571) (wrong : w 5 = 1541) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints Tests.Keccak.permissiveSetup) := by
  intro h
  obtain ⟨s, decoded, next⟩ := (Keccak.control_updates (by decide) h).active active
  rw [input] at decoded
  rw [wrong] at next
  have literal : (1571 : ZMod babyBearModulus).val = 1571 := by decide
  rw [literal] at decoded
  have modeBound := s.mode.isLt
  have iterationBound := s.iteration.isLt
  have roundBound := s.round.isLt
  unfold Keccak.ControlState.packed at decoded
  have values : s.mode.val = 3 ∧ s.iteration.val = 4 ∧ s.round.val = 24 := by omega
  have literalWrong : (1541 : ZMod babyBearModulus).val = 1541 := by decide
  rw [literalWrong] at next
  simp [Keccak.ControlState.nextPacked, values.1, values.2.1, values.2.2] at next

end Tests.KeccakControlUpdate
