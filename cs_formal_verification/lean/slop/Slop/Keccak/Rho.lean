module
public import Slop.Keccak.RhoRotation
public import Slop.Keccak.Theta
public import Slop.Keccak.Lanes

@[expose] public section

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

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

theorem rho_written_bounds {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
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

end Airbender.Keccak.Proofs
