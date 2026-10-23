import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Keccak.RhoRotation
import Airbender.Proofs.Keccak.Theta
import Airbender.Proofs.Keccak.Lanes

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem rho_reference (state : Vector Nat 25) (column operation : Fin 5) :
    (Specs.Keccak256.rhoPi state)[rhoDestinations[column][operation]] =
      rotLeft64 state[5 * column.val + operation.val] Rho.rotations[column][operation] := by
  fin_cases column <;> fin_cases operation <;>
    simp [Specs.Keccak256.rhoPi, rhoDestinations, Rho.rotations, rhoRotations]

theorem rho_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 67 = 1) : writeLaneLimbs w 5 = readLaneLimbs w 5 := by
  apply Vector.ext
  intro i hi
  have equation := Verification.assertion_of_holds h ⟨128 + i, by rw [constraint_count]; omega⟩
  interval_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, writeLaneLimbs, readLaneLimbs] at equation ⊢
  all_goals linear_combination -equation

theorem rho_written_bounds {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 67 = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536)
    (lane : Fin 6) (limb : Fin 4) :
    (w (17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
  by_cases scratch : lane.val = 5
  · have same : lane = 5 := Fin.ext scratch
    subst lane
    have equal := congrArg (fun v : Vector (ZMod p) 4 => v[limb]) (rho_preserved h selected)
    have bound := reads 5 limb
    fin_cases limb
    all_goals simp [readLaneLimbs, writeLaneLimbs] at equal
    all_goals simpa [equal] using bound
  · have small : lane.val < 5 := by omega
    let op : Fin 5 := ⟨lane.val, small⟩
    obtain ⟨s, input, _⟩ := (control_update_checks (by omega) h).active active
    have decoded := decoded_control (by omega) s h active input
    have bounds (i : Fin 4) : (Rho.rhoLimbs w op)[i] < 65536 := by
      rw [Rho.rho_limbs_at]
      exact reads lane i
    have value := Rho.rho_rotated_limb hp s.iteration h active selected decoded.2.1 op bounds limb
    change (w (17 + 8 * op.val + Rho.limbOffset[limb])).val < 65536
    rw [value]
    exact rotated_lane_limb_bound bounds Rho.rotations[s.iteration][op] limb

theorem theta_rho_column {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {theta rho : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5} {round : Fin 24}
    (thetaHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment theta)
      (importedConstraints (setupTable control)))
    (rhoHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment rho)
      (importedConstraints (setupTable control)))
    (mapping : ThetaRhoMapping state d column round theta rho) : RhoResult state d column rho := by
  have thetaDecoded := decoded_control (by omega) (ControlState.mk 3 column ⟨round.val, by omega⟩)
    thetaHolds mapping.thetaActive mapping.thetaControl
  have rhoDecoded := decoded_control (by omega) (ControlState.mk 4 column ⟨round.val, by omega⟩)
    rhoHolds mapping.rhoActive mapping.rhoControl
  have thetaSelected : theta 66 = 1 := by
    simpa [Variables.modeColumns] using thetaDecoded.1 (3 : Fin 7)
  have rhoSelected : rho 67 = 1 := by
    simpa [Variables.modeColumns] using rhoDecoded.1 (4 : Fin 7)
  have thetaResult := (theta_column (by omega) thetaHolds
    (show ThetaInterface state d column theta from
      ⟨mapping.thetaActive, thetaSelected, mapping.stateReads, mapping.dRead⟩)).1
  have bounds (operation : Fin 5) (limb : Fin 4) : (Rho.rhoLimbs rho operation)[limb] < 65536 := by
    have value := congrArg (fun v : Vector (ZMod p) 4 => v[limb]) (mapping.transport operation)
    have bounded := (theta_limb_xors (by omega) thetaHolds mapping.thetaActive thetaSelected
      operation limb).2.2.1
    change (theta (17 + 8 * operation.val + Rho.limbOffset[limb])).val < 65536 at bounded
    have field : (writeLaneLimbs theta ⟨operation.val, by omega⟩)[limb] =
        theta (17 + 8 * operation.val + Rho.limbOffset[limb]) := by
      fin_cases limb <;> simp [writeLaneLimbs, Rho.limbOffset] <;> congr 1 <;> omega
    rw [← field] at bounded
    have mapped : (Rho.rhoLimbs rho operation)[limb] =
        (readLaneLimbs rho ⟨operation.val, by omega⟩)[limb].val := by
      fin_cases limb <;> simp [Rho.rhoLimbs, readLaneLimbs]
    rw [mapped, value]
    exact bounded
  refine ⟨?_, rho_preserved rhoHolds rhoSelected⟩
  intro operation
  have rotation := Rho.rho_rotated_lane hp column rhoHolds mapping.rhoActive rhoSelected
    rhoDecoded.2.1 operation (bounds operation)
  rw [rho_reference, rotation, lane_of_limbs (mapping.transport operation), thetaResult operation]

end Airbender.Keccak.Proofs
