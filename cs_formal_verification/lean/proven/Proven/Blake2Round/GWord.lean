module
public import Proven.Arithmetic.Chunks

@[expose] public section

set_option warningAsError true

/-!
Word-level stages of the wider-table G function, over plain natural numbers.
Each lemma turns chunk facts (bounds, chunk XORs, limb sums) into one step of
Clean's G reference: a modular addition or an XOR followed by a rotation.
-/

namespace Airbender.Blake2Round.Proofs

open Arithmetic

set_option maxHeartbeats 2000000

/-- Two limb sums with carries give the 32-bit sum of three words. -/
theorem add3_of_limbs {aL aH bL bH xL xH rL rH k0 k1 : Nat}
    (rLB : rL < 65536) (rHB : rH < 65536)
    (low : aL + bL + xL = rL + 65536 * k0) (high : aH + bH + xH + k0 = rH + 65536 * k1) :
    rL + 65536 * rH = add32 (aL + 65536 * aH) (add32 (bL + 65536 * bH) (xL + 65536 * xH)) := by
  unfold add32
  omega

/-- Two limb sums with carries give the 32-bit sum of two words. -/
theorem add2_of_limbs {cL cH dL dH rL rH k0 k1 : Nat}
    (rLB : rL < 65536) (rHB : rH < 65536)
    (low : cL + dL = rL + 65536 * k0) (high : cH + dH + k0 = rH + 65536 * k1) :
    rL + 65536 * rH = add32 (cL + 65536 * cH) (dL + 65536 * dH) := by
  unfold add32
  omega

/-- XOR of two words given by bytes is the word of the byte XORs. -/
theorem xor_of_bytes {u0 u1 u2 u3 e0 e1 e2 e3 : Nat}
    (u0B : u0 < 256) (u1B : u1 < 256) (u2B : u2 < 256)
    (e0B : e0 < 256) (e1B : e1 < 256) (e2B : e2 < 256) :
    ((u0 + 256 * u1) + 65536 * (u2 + 256 * u3)) ^^^ ((e0 + 256 * e1) + 65536 * (e2 + 256 * e3)) =
      (u0 ^^^ e0) + 256 * ((u1 ^^^ e1) + 256 * ((u2 ^^^ e2) + 256 * (u3 ^^^ e3))) := by
  have full := xor_of_chunks (width := 8) (a₀ := u0) (b₀ := e0)
    (a₁ := u1 + 256 * (u2 + 256 * u3)) (b₁ := e1 + 256 * (e2 + 256 * e3)) u0B e0B
  have mid := xor_of_chunks (width := 8) (a₀ := u1) (b₀ := e1)
    (a₁ := u2 + 256 * u3) (b₁ := e2 + 256 * e3) u1B e1B
  have top := xor_of_chunks (width := 8) (a₀ := u2) (b₀ := e2) (a₁ := u3) (b₁ := e3) u2B e2B
  norm_num only [Nat.reducePow] at full mid top
  rw [show (u0 + 256 * u1) + 65536 * (u2 + 256 * u3) = u0 + 256 * (u1 + 256 * (u2 + 256 * u3)) by ring,
    show (e0 + 256 * e1) + 65536 * (e2 + 256 * e3) = e0 + 256 * (e1 + 256 * (e2 + 256 * e3)) by ring,
    full, mid, top]

/-- `rotate_right::<16>` of a byte-wise XOR. -/
theorem rotate16_of_bytes {u0 u1 u2 u3 e0 e1 e2 e3 y0 y1 y2 y3 : Nat}
    (u0B : u0 < 256) (u1B : u1 < 256) (u2B : u2 < 256)
    (e0B : e0 < 256) (e1B : e1 < 256) (e2B : e2 < 256)
    (x0 : y0 = u0 ^^^ e0) (x1 : y1 = u1 ^^^ e1) (x2 : y2 = u2 ^^^ e2) (x3 : y3 = u3 ^^^ e3)
    (y0B : y0 < 256) (y1B : y1 < 256) :
    rotRight32 (((u0 + 256 * u1) + 65536 * (u2 + 256 * u3)) ^^^
      ((e0 + 256 * e1) + 65536 * (e2 + 256 * e3))) 16 =
      (y2 + 256 * y3) + 65536 * (y0 + 256 * y1) := by
  rw [xor_of_bytes u0B u1B u2B e0B e1B e2B, ← x0, ← x1, ← x2, ← x3]
  have rotation := rotate_right_of_chunks (width := 16) (by decide)
    (show y0 + 256 * y1 < 2 ^ 16 by norm_num; omega) (high := y2 + 256 * y3)
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [show y0 + 256 * (y1 + 256 * (y2 + 256 * y3)) = y0 + 256 * y1 + 65536 * (y2 + 256 * y3) by ring,
    rotation]
  ring

/-- `rotate_right::<8>` of a byte-wise XOR. -/
theorem rotate8_of_bytes {u0 u1 u2 u3 e0 e1 e2 e3 y0 y1 y2 y3 : Nat}
    (u0B : u0 < 256) (u1B : u1 < 256) (u2B : u2 < 256)
    (e0B : e0 < 256) (e1B : e1 < 256) (e2B : e2 < 256)
    (x0 : y0 = u0 ^^^ e0) (x1 : y1 = u1 ^^^ e1) (x2 : y2 = u2 ^^^ e2) (x3 : y3 = u3 ^^^ e3)
    (y0B : y0 < 256) :
    rotRight32 (((u0 + 256 * u1) + 65536 * (u2 + 256 * u3)) ^^^
      ((e0 + 256 * e1) + 65536 * (e2 + 256 * e3))) 8 =
      (y1 + 256 * y2) + 65536 * (y3 + 256 * y0) := by
  rw [xor_of_bytes u0B u1B u2B e0B e1B e2B, ← x0, ← x1, ← x2, ← x3]
  have rotation := rotate_right_of_chunks (width := 8) (by decide)
    (show y0 < 2 ^ 8 by norm_num; omega) (high := y1 + 256 * (y2 + 256 * y3))
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [rotation]
  ring

/-- The split 4+3 table row is the 7-bit number `xor4 + 16 * xor3`. -/
theorem split_xor {a b c d : Nat} (ha : a < 16) (hc : c < 16) :
    (a ^^^ c) ||| ((b ^^^ d) <<< 4) = (a ^^^ c) + 16 * (b ^^^ d) := by
  have low : a ^^^ c < 2 ^ 4 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt low, Nat.shiftLeft_eq]
  ring

/-- `rotate_right::<12>` with 3/9/4-bit chunks; the 4-bit XOR of one limb and
    the 3-bit XOR of the other come from one split table row. -/
theorem rotate12_of_chunks {b3l b9l b4l b3h b9h b4h c3l c9l c4l c3h c9h c4h
      x9l x9h x7l x7h : Nat}
    (b3lB : b3l < 8) (b9lB : b9l < 512) (b4lB : b4l < 16)
    (b3hB : b3h < 8) (b9hB : b9h < 512) (b4hB : b4h < 16)
    (c3lB : c3l < 8) (c9lB : c9l < 512) (c4lB : c4l < 16)
    (c3hB : c3h < 8) (c9hB : c9h < 512) (c4hB : c4h < 16)
    (x9lE : x9l = b9l ^^^ c9l) (x9hE : x9h = b9h ^^^ c9h)
    (x7lE : x7l = (b4l ^^^ c4l) ||| ((b3h ^^^ c3h) <<< 4))
    (x7hE : x7h = (b4h ^^^ c4h) ||| ((b3l ^^^ c3l) <<< 4)) :
    rotRight32 (((b3l + 8 * b9l + 4096 * b4l) + 65536 * (b3h + 8 * b9h + 4096 * b4h)) ^^^
      ((c3l + 8 * c9l + 4096 * c4l) + 65536 * (c3h + 8 * c9h + 4096 * c4h))) 12 =
      (x7l + 128 * x9h) + 65536 * (x7h + 128 * x9l) := by
  rw [x7lE, x7hE, split_xor b4lB c4lB, split_xor b4hB c4hB, x9lE, x9hE]
  have z3l : b3l ^^^ c3l < 8 := Nat.xor_lt_two_pow (n := 3) b3lB c3lB
  have z9l : b9l ^^^ c9l < 512 := Nat.xor_lt_two_pow (n := 9) b9lB c9lB
  have z3h : b3h ^^^ c3h < 8 := Nat.xor_lt_two_pow (n := 3) b3hB c3hB
  have z9h : b9h ^^^ c9h < 512 := Nat.xor_lt_two_pow (n := 9) b9hB c9hB
  have z4l : b4l ^^^ c4l < 16 := Nat.xor_lt_two_pow (n := 4) b4lB c4lB
  have z4h : b4h ^^^ c4h < 16 := Nat.xor_lt_two_pow (n := 4) b4hB c4hB
  have full := xor_of_chunks (width := 16) (a₀ := b3l + 8 * b9l + 4096 * b4l)
    (b₀ := c3l + 8 * c9l + 4096 * c4l) (a₁ := b3h + 8 * b9h + 4096 * b4h)
    (b₁ := c3h + 8 * c9h + 4096 * c4h) (by norm_num; omega) (by norm_num; omega)
  have limb {t3 t9 t4 s3 s9 s4 : Nat} (t3B : t3 < 8) (s3B : s3 < 8)
      (t9B : t9 < 512) (s9B : s9 < 512) :
      (t3 + 8 * t9 + 4096 * t4) ^^^ (s3 + 8 * s9 + 4096 * s4) =
        (t3 ^^^ s3) + 8 * ((t9 ^^^ s9) + 512 * (t4 ^^^ s4)) := by
    have one := xor_of_chunks (width := 3) (a₀ := t3) (b₀ := s3) (a₁ := t9 + 512 * t4)
      (b₁ := s9 + 512 * s4) t3B s3B
    have two := xor_of_chunks (width := 9) (a₀ := t9) (b₀ := s9) (a₁ := t4) (b₁ := s4) t9B s9B
    norm_num only [Nat.reducePow] at one two
    rw [show t3 + 8 * t9 + 4096 * t4 = t3 + 8 * (t9 + 512 * t4) by ring,
      show s3 + 8 * s9 + 4096 * s4 = s3 + 8 * (s9 + 512 * s4) by ring, one, two]
  norm_num only [Nat.reducePow] at full
  rw [full, limb b3lB c3lB b9lB c9lB, limb b3hB c3hB b9hB c9hB]
  have rotation := rotate_right_of_chunks (width := 12) (by decide)
    (show (b3l ^^^ c3l) + 8 * (b9l ^^^ c9l) < 2 ^ 12 by norm_num; omega)
    (high := (b4l ^^^ c4l) + 16 * ((b3h ^^^ c3h) + 8 * (b9h ^^^ c9h) + 4096 * (b4h ^^^ c4h)))
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [show (b3l ^^^ c3l) + 8 * ((b9l ^^^ c9l) + 512 * (b4l ^^^ c4l)) +
      65536 * ((b3h ^^^ c3h) + 8 * ((b9h ^^^ c9h) + 512 * (b4h ^^^ c4h))) =
      (b3l ^^^ c3l) + 8 * (b9l ^^^ c9l) + 4096 * ((b4l ^^^ c4l) + 16 *
        ((b3h ^^^ c3h) + 8 * (b9h ^^^ c9h) + 4096 * (b4h ^^^ c4h))) by ring, rotation]
  ring

/-- `rotate_right::<7>` with 7/9-bit chunks of both limbs. -/
theorem rotate7_of_chunks {u0 u1 u2 u3 e0 e1 e2 e3 z0 z1 z2 z3 : Nat}
    (u0B : u0 < 128) (u1B : u1 < 512) (u2B : u2 < 128)
    (e0B : e0 < 128) (e1B : e1 < 512) (e2B : e2 < 128)
    (x0 : z0 = u0 ^^^ e0) (x1 : z1 = u1 ^^^ e1) (x2 : z2 = u2 ^^^ e2) (x3 : z3 = u3 ^^^ e3) :
    rotRight32 (((u0 + 128 * u1) + 65536 * (u2 + 128 * u3)) ^^^
      ((e0 + 128 * e1) + 65536 * (e2 + 128 * e3))) 7 =
      (z1 + 512 * z2) + 65536 * (z3 + 512 * z0) := by
  have z0B : z0 < 128 := x0 ▸ Nat.xor_lt_two_pow (n := 7) u0B e0B
  have z1B : z1 < 512 := x1 ▸ Nat.xor_lt_two_pow (n := 9) u1B e1B
  have full := xor_of_chunks (width := 7) (a₀ := u0) (b₀ := e0)
    (a₁ := u1 + 512 * (u2 + 128 * u3)) (b₁ := e1 + 512 * (e2 + 128 * e3)) u0B e0B
  have mid := xor_of_chunks (width := 9) (a₀ := u1) (b₀ := e1)
    (a₁ := u2 + 128 * u3) (b₁ := e2 + 128 * e3) u1B e1B
  have top := xor_of_chunks (width := 7) (a₀ := u2) (b₀ := e2) (a₁ := u3) (b₁ := e3) u2B e2B
  norm_num only [Nat.reducePow] at full mid top
  rw [show (u0 + 128 * u1) + 65536 * (u2 + 128 * u3) = u0 + 128 * (u1 + 512 * (u2 + 128 * u3)) by ring,
    show (e0 + 128 * e1) + 65536 * (e2 + 128 * e3) = e0 + 128 * (e1 + 512 * (e2 + 128 * e3)) by ring,
    full, mid, top, ← x0, ← x1, ← x2, ← x3]
  have rotation := rotate_right_of_chunks (width := 7) (by decide)
    (show z0 < 2 ^ 7 by norm_num; omega) (high := z1 + 512 * (z2 + 128 * z3))
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [rotation]
  ring

end Airbender.Blake2Round.Proofs
