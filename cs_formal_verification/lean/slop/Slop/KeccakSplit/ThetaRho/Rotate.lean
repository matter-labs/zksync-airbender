module
public import Slop.KeccakSplit.ThetaRho.ByteLane
public import Human.Circuits.KeccakSplit.Call

@[expose] public section

/- The byte-fragment rotation is the 64-bit rotation, for every offset: the 16-bit limb rotation
   (`rotate_left_of_limbs`) splits into the byte fragments, one byte pair per limb. -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Arithmetic
set_option warningAsError true

/-- The 16-bit limbs of eight bytes, as `pack_byte_pairs` pairs them. -/
def byteLimbs (bytes : Vector Nat 8) : Vector Nat 4 :=
  Vector.ofFn fun limb : Fin 4 =>
    bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] + 256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]

/-- One rotated 16-bit limb is the pair of its two rotated bytes. -/
theorem rotated_limb_bytes {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256)
    (left : Fin 64) (limb : Fin 4) :
    rotatedLaneLimb (byteLimbs bytes) left limb =
      rotatedLaneByte bytes left ⟨2 * limb.val, by omega⟩ +
        256 * rotatedLaneByte bytes left ⟨2 * limb.val + 1, by omega⟩ := by
  have bound (digit : Nat) (valid : digit < 8) : bytes[digit] < 256 := by
    simpa only [Fin.getElem_fin] using bounds ⟨digit, valid⟩
  have limbBound := limb.isLt
  have leftBound := left.isLt
  simp only [rotatedLaneLimb, rotatedLaneByte, rotationSource, rotationPrevious, byteRotationSource,
    byteRotationPrevious, byteLimbs, Vector.getElem_ofFn, Fin.getElem_fin]
  obtain ⟨source, hsource⟩ : ∃ source, source = (limb.val + 4 - left.val / 16) % 4 := ⟨_, rfl⟩
  obtain ⟨prior, hprior⟩ : ∃ prior, prior = (source + 3) % 4 := ⟨_, rfl⟩
  simp only [← hsource, ← hprior]
  have a0 := bound (2 * source) (by omega)
  have a1 := bound (2 * source + 1) (by omega)
  have b0 := bound (2 * prior) (by omega)
  have b1 := bound (2 * prior + 1) (by omega)
  by_cases low : left.val % 16 < 8
  · simp only [show (2 * limb.val + 8 - left.val / 8) % 8 = 2 * source by omega,
      show (2 * limb.val + 1 + 8 - left.val / 8) % 8 = 2 * source + 1 by omega,
      show (2 * source + 7) % 8 = 2 * prior + 1 by omega,
      show (2 * source + 1 + 7) % 8 = 2 * source by omega,
      show left.val % 8 = left.val % 16 by omega]
    generalize bytes[2 * source] = x0 at a0 ⊢
    generalize bytes[2 * source + 1] = x1 at a1 ⊢
    generalize bytes[2 * prior] = y0 at b0 ⊢
    generalize bytes[2 * prior + 1] = y1 at b1 ⊢
    generalize left.val % 16 = shift at low ⊢
    interval_cases shift <;> norm_num <;> omega
  · simp only [show (2 * limb.val + 8 - left.val / 8) % 8 = 2 * prior + 1 by omega,
      show (2 * limb.val + 1 + 8 - left.val / 8) % 8 = 2 * source by omega,
      show (2 * prior + 1 + 7) % 8 = 2 * prior by omega,
      show (2 * source + 7) % 8 = 2 * prior + 1 by omega,
      show left.val % 8 = left.val % 16 - 8 by omega]
    generalize bytes[2 * source] = x0 at a0 ⊢
    generalize bytes[2 * source + 1] = x1 at a1 ⊢
    generalize bytes[2 * prior] = y0 at b0 ⊢
    generalize bytes[2 * prior + 1] = y1 at b1 ⊢
    have shiftBound : left.val % 16 < 16 := Nat.mod_lt _ (by decide)
    generalize left.val % 16 = shift at low shiftBound ⊢
    interval_cases shift <;> norm_num <;> omega

/-- The byte-fragment rotation is the 64-bit rotation for every offset. -/
theorem rotate_bytes {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256)
    (left : Fin 64) :
    rotLeft64 (packByteLane bytes) left =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes left)) := by
  have limbBounds (limb : Fin 4) : (byteLimbs bytes)[limb] < 65536 := by
    have low := bounds ⟨2 * limb.val, by omega⟩
    have high := bounds ⟨2 * limb.val + 1, by omega⟩
    simp only [byteLimbs, Fin.getElem_fin, Vector.getElem_ofFn] at low high ⊢
    omega
  rw [← pack_byte_pairs bytes, ← pack_byte_pairs]
  change rotLeft64 (packLane (byteLimbs bytes)) left = _
  rw [rotate_left_of_limbs limbBounds]
  congr 1
  apply Vector.ext
  intro limb bound
  simp only [Vector.getElem_map, Vector.getElem_finRange, Vector.getElem_ofFn, Fin.getElem_fin]
  exact rotated_limb_bytes bounds left ⟨limb, bound⟩

/-- The byte-fragment rotation is the 64-bit rotation for every rho offset. -/
theorem rotate_rho {bytes : Vector Nat 8} (bounds : ∀ digit : Fin 8, bytes[digit] < 256)
    (column lane : Fin 5) :
    rotLeft64 (packByteLane bytes) (Call.rotations[column][lane]) =
      packByteLane ((Vector.finRange 8).map (rotatedLaneByte bytes (Call.rotations[column][lane]))) :=
  rotate_bytes bounds _

end Airbender.Keccak.Split.ThetaRho.Proofs
