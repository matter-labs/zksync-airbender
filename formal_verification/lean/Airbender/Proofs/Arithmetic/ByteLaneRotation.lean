import Airbender.Proofs.Arithmetic.LaneRotation

namespace Airbender.Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Eight canonical bytes form one complete sixty-four-bit lane. -/
def packByteLane (bytes : Vector Nat 8) : Nat :=
  bytes[0] + 256 * (bytes[1] + 256 * (bytes[2] + 256 * (bytes[3] +
    256 * (bytes[4] + 256 * (bytes[5] + 256 * (bytes[6] + 256 * bytes[7]))))))

/-- The source byte after the complete-byte part of a left rotation. -/
def byteRotationSource (left : Fin 64) (digit : Fin 8) : Fin 8 :=
  ⟨(digit.val + 8 - left.val / 8) % 8, by omega⟩

/-- The previous cyclic source byte supplies the overflow fragment. -/
def byteRotationPrevious (digit : Fin 8) : Fin 8 := ⟨(digit.val + 7) % 8, by omega⟩

/-- Exact low and high fragments form one byte of the original lane rotation. -/
def rotatedLaneByte (bytes : Vector Nat 8) (left : Fin 64) (digit : Fin 8) : Nat :=
  let source := byteRotationSource left digit
  (bytes[source] * 2 ^ (left.val % 8)) % 256 +
    bytes[byteRotationPrevious source] / 2 ^ (8 - left.val % 8)

/-- Canonical byte bounds give the complete lane bound. -/
theorem pack_byte_lane_bound {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256) :
    packByteLane bytes < 2 ^ 64 := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  unfold packByteLane
  norm_num only [Nat.reducePow]
  omega

/-- The two exact native-style fragments always form one canonical byte. -/
theorem rotated_lane_byte_bound {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256)
    (left : Fin 64) (digit : Fin 8) : rotatedLaneByte bytes left digit < 256 := by
  have current := bounds (byteRotationSource left digit)
  have prior := bounds (byteRotationPrevious (byteRotationSource left digit))
  dsimp only [rotatedLaneByte]
  generalize bytes[byteRotationSource left digit] = a at current ⊢
  generalize bytes[byteRotationPrevious (byteRotationSource left digit)] = b at prior ⊢
  have small : left.val % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize left.val % 8 = remainder at small ⊢
  interval_cases remainder <;> norm_num <;> omega

private theorem rotate_group0 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨0 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨0 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group1 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨8 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨8 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group2 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨16 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨16 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group3 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨24 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨24 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group4 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨32 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨32 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group5 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨40 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨40 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group6 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨48 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨48 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

private theorem rotate_group7 {bytes : Vector Nat 8}
    (bounds : ∀ digit : Fin 8, bytes[digit] < 256) (low : Fin 8) :
    rotLeft64 (packByteLane bytes) ⟨56 + low.val, by have := low.isLt; omega⟩ =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes ⟨56 + low.val, by have := low.isLt; omega⟩)) := by
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  have h4 := bounds 4; have h5 := bounds 5; have h6 := bounds 6; have h7 := bounds 7
  change bytes[(0 : Nat)] < 256 at h0
  change bytes[(1 : Nat)] < 256 at h1
  change bytes[(2 : Nat)] < 256 at h2
  change bytes[(3 : Nat)] < 256 at h3
  change bytes[(4 : Nat)] < 256 at h4
  change bytes[(5 : Nat)] < 256 at h5
  change bytes[(6 : Nat)] < 256 at h6
  change bytes[(7 : Nat)] < 256 at h7
  fin_cases low <;>
    dsimp [packByteLane, rotatedLaneByte, byteRotationSource, byteRotationPrevious,
      rotLeft64, rotRight64] <;>
    simp [rotatedLaneByte, byteRotationSource, byteRotationPrevious] <;> omega

/-- The complete byte-fragment construction equals the unchanged original sixty-four-bit rotation. -/
theorem rotate_left_of_bytes {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256)
    (left : Fin 64) :
    rotLeft64 (packByteLane bytes) left =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes left)) := by
  fin_cases left
  · exact rotate_group0 bounds 0
  · exact rotate_group0 bounds 1
  · exact rotate_group0 bounds 2
  · exact rotate_group0 bounds 3
  · exact rotate_group0 bounds 4
  · exact rotate_group0 bounds 5
  · exact rotate_group0 bounds 6
  · exact rotate_group0 bounds 7
  · exact rotate_group1 bounds 0
  · exact rotate_group1 bounds 1
  · exact rotate_group1 bounds 2
  · exact rotate_group1 bounds 3
  · exact rotate_group1 bounds 4
  · exact rotate_group1 bounds 5
  · exact rotate_group1 bounds 6
  · exact rotate_group1 bounds 7
  · exact rotate_group2 bounds 0
  · exact rotate_group2 bounds 1
  · exact rotate_group2 bounds 2
  · exact rotate_group2 bounds 3
  · exact rotate_group2 bounds 4
  · exact rotate_group2 bounds 5
  · exact rotate_group2 bounds 6
  · exact rotate_group2 bounds 7
  · exact rotate_group3 bounds 0
  · exact rotate_group3 bounds 1
  · exact rotate_group3 bounds 2
  · exact rotate_group3 bounds 3
  · exact rotate_group3 bounds 4
  · exact rotate_group3 bounds 5
  · exact rotate_group3 bounds 6
  · exact rotate_group3 bounds 7
  · exact rotate_group4 bounds 0
  · exact rotate_group4 bounds 1
  · exact rotate_group4 bounds 2
  · exact rotate_group4 bounds 3
  · exact rotate_group4 bounds 4
  · exact rotate_group4 bounds 5
  · exact rotate_group4 bounds 6
  · exact rotate_group4 bounds 7
  · exact rotate_group5 bounds 0
  · exact rotate_group5 bounds 1
  · exact rotate_group5 bounds 2
  · exact rotate_group5 bounds 3
  · exact rotate_group5 bounds 4
  · exact rotate_group5 bounds 5
  · exact rotate_group5 bounds 6
  · exact rotate_group5 bounds 7
  · exact rotate_group6 bounds 0
  · exact rotate_group6 bounds 1
  · exact rotate_group6 bounds 2
  · exact rotate_group6 bounds 3
  · exact rotate_group6 bounds 4
  · exact rotate_group6 bounds 5
  · exact rotate_group6 bounds 6
  · exact rotate_group6 bounds 7
  · exact rotate_group7 bounds 0
  · exact rotate_group7 bounds 1
  · exact rotate_group7 bounds 2
  · exact rotate_group7 bounds 3
  · exact rotate_group7 bounds 4
  · exact rotate_group7 bounds 5
  · exact rotate_group7 bounds 6
  · exact rotate_group7 bounds 7

end Airbender.Arithmetic
