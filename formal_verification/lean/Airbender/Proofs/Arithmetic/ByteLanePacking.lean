import Airbender.Proofs.Arithmetic.ByteLaneRotation

namespace Airbender.Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Four consecutive byte pairs give the same complete sixty-four-bit lane. -/
theorem pack_byte_pairs (bytes : Vector Nat 8) :
    packLane (Vector.ofFn fun limb : Fin 4 =>
      bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] +
        256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) = packByteLane bytes := by
  simp [packLane, packByteLane]
  ring

/-- Exact XOR on all eight byte pairs gives the complete lane XOR. -/
theorem pack_byte_lane_xor {a b : Vector Nat 8}
    (aBound : ∀ digit : Fin 8, a[digit] < 256) (bBound : ∀ digit : Fin 8, b[digit] < 256) :
    packByteLane (Vector.ofFn fun digit : Fin 8 => a[digit] ^^^ b[digit]) =
      packByteLane a ^^^ packByteLane b := by
  have ha (digit : Nat) (valid : digit < 8) : a[digit] < 256 := by
    simpa only [Fin.getElem_fin] using aBound ⟨digit, valid⟩
  have hb (digit : Nat) (valid : digit < 8) : b[digit] < 256 := by
    simpa only [Fin.getElem_fin] using bBound ⟨digit, valid⟩
  have chunks {a₀ a₁ b₀ b₁ : Nat} (aBound : a₀ < 256) (bBound : b₀ < 256) :
      (a₀ + 256 * a₁) ^^^ (b₀ + 256 * b₁) = (a₀ ^^^ b₀) + 256 * (a₁ ^^^ b₁) := by
    have result := xor_of_chunks (width := 8) (a₁ := a₁) (b₁ := b₁) aBound bBound
    norm_num only [Nat.reducePow] at result
    exact result
  unfold packByteLane
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  rw [chunks (ha 0 (by decide)) (hb 0 (by decide)),
    chunks (ha 1 (by decide)) (hb 1 (by decide)),
    chunks (ha 2 (by decide)) (hb 2 (by decide)),
    chunks (ha 3 (by decide)) (hb 3 (by decide)),
    chunks (ha 4 (by decide)) (hb 4 (by decide)),
    chunks (ha 5 (by decide)) (hb 5 (by decide)),
    chunks (ha 6 (by decide)) (hb 6 (by decide))]

end Airbender.Arithmetic
