import Slop.Arithmetic.ByteAssembly
import Mathlib.Tactic.IntervalCases

namespace Airbender.Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4800000

def packLane (limbs : Vector Nat 4) : Nat :=
  limbs[0] + 65536 * (limbs[1] + 65536 * (limbs[2] + 65536 * limbs[3]))

def rotationSource (left : Fin 64) (limb : Fin 4) : Fin 4 :=
  ⟨(limb.val + 4 - left.val / 16) % 4, by omega⟩

def rotationPrevious (limb : Fin 4) : Fin 4 := ⟨(limb.val + 3) % 4, by omega⟩

def rotatedLaneLimb (limbs : Vector Nat 4) (left : Fin 64) (limb : Fin 4) : Nat :=
  let source := rotationSource left limb
  (limbs[source] * 2 ^ (left.val % 16)) % 65536 +
    limbs[rotationPrevious source] / 2 ^ (16 - left.val % 16)

theorem rotated_lane_limb_bound {limbs : Vector Nat 4}
    (bounds : ∀ i : Fin 4, limbs[i] < 65536) (left : Fin 64) (limb : Fin 4) :
    rotatedLaneLimb limbs left limb < 65536 := by
  have current := bounds (rotationSource left limb)
  have prior := bounds (rotationPrevious (rotationSource left limb))
  dsimp only [rotatedLaneLimb]
  generalize limbs[rotationSource left limb] = a at current ⊢
  generalize limbs[rotationPrevious (rotationSource left limb)] = b at prior ⊢
  have small : left.val % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize left.val % 16 = r at small ⊢
  interval_cases r <;> norm_num <;> omega

theorem rotate_left_of_limbs {limbs : Vector Nat 4}
    (bounds : ∀ i : Fin 4, limbs[i] < 65536) (left : Fin 64) :
    rotLeft64 (packLane limbs) left =
      packLane ((Vector.finRange 4).map (rotatedLaneLimb limbs left)) := by
  have h0 := bounds 0; have h1 := bounds 1
  have h2 := bounds 2; have h3 := bounds 3
  change limbs[(0 : Nat)] < 65536 at h0
  change limbs[(1 : Nat)] < 65536 at h1
  change limbs[(2 : Nat)] < 65536 at h2
  change limbs[(3 : Nat)] < 65536 at h3
  fin_cases left <;>
    dsimp [packLane, rotatedLaneLimb, rotationSource, rotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneLimb, rotationSource, rotationPrevious] <;> omega

end Airbender.Arithmetic
