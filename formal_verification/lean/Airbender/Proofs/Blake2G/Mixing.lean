import Airbender.Proofs.Blake2G
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Blake2G.Proofs

open Arithmetic

set_option maxHeartbeats 1200000

-- These are intermediate field expressions from the imported queries, not a
-- second G specification. The target operation is Clean's native reference.
private def firstAlo {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  w 15 + w 19 + w 33 - 65536 * w 37 - 131072 * w 38

private def firstAhi {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  w 16 + w 20 + w 34 + w 37 + 2 * w 38 - 65536 * w 39 - 131072 * w 40

private theorem inverse256 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    256 * (-7864320 : ZMod p) = 1 := by
  linear_combination compatible

private def byteXor {p : Nat} (x y z : ZMod p) : Prop :=
  x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = x.val ^^^ y.val

private theorem first_xors {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) :
    byteXor (w 43) (w 41) (w 44) ∧
    byteXor ((-7864320 : ZMod p) * (w 27 - w 43))
      ((-7864320 : ZMod p) * (firstAlo w - w 41)) (w 45) ∧
    byteXor (w 46) (w 42) (w 47) ∧
    byteXor ((-7864320 : ZMod p) * (w 28 - w 46))
      ((-7864320 : ZMod p) * (firstAhi w - w 42)) (w 48) := by
  have q0 := data_lookups (by omega) h (0 : Fin 18)
  have q1 := data_lookups (by omega) h (1 : Fin 18)
  have q2 := data_lookups (by omega) h (2 : Fin 18)
  have q3 := data_lookups (by omega) h (3 : Fin 18)
  simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment] at q0 q1 q2 q3
  have inv := inverse256 compatible
  have loQuery : -(7864320 * w 15) + -(7864320 * w 19) + -(7864320 * w 33) +
      -(256 * w 37) + -(512 * w 38) + 7864320 * w 41 =
      (-7864320 : ZMod p) * (firstAlo w - w 41) := by
    unfold firstAlo
    linear_combination (256 * w 37 + 512 * w 38) * inv
  have hiQuery : -(7864320 * w 16) + -(7864320 * w 20) + -(7864320 * w 34) +
      -(7864320 * w 37) + -(15728640 * w 38) + -(256 * w 39) + -(512 * w 40) +
      7864320 * w 42 = (-7864320 : ZMod p) * (firstAhi w - w 42) := by
    unfold firstAhi
    linear_combination (256 * w 39 + 512 * w 40) * inv
  have dLoQuery : -(7864320 * w 27) + 7864320 * w 43 =
      (-7864320 : ZMod p) * (w 27 - w 43) := by ring
  have dHiQuery : -(7864320 * w 28) + 7864320 * w 46 =
      (-7864320 : ZMod p) * (w 28 - w 46) := by ring
  rw [dLoQuery] at q1
  rw [dHiQuery] at q3
  rw [loQuery] at q1
  rw [hiQuery] at q3
  exact ⟨q0, q1, q2, q3⟩

/-- Recover the byte splits of the first addition and the incoming d word from
    the four actual imported XOR queries. -/
theorem first_byte_splits {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) :
    (firstAlo w).val = (w 41).val + 256 * ((-7864320 : ZMod p) * (firstAlo w - w 41)).val ∧
    (firstAhi w).val = (w 42).val + 256 * ((-7864320 : ZMod p) * (firstAhi w - w 42)).val ∧
    (w 27).val = (w 43).val + 256 * ((-7864320 : ZMod p) * (w 27 - w 43)).val ∧
    (w 28).val = (w 46).val + 256 * ((-7864320 : ZMod p) * (w 28 - w 46)).val := by
  obtain ⟨q0, q1, q2, q3⟩ := first_xors hp compatible h
  have inv := inverse256 compatible
  exact ⟨value_of_scaled_chunks hp inv q0.2.1 q1.2.1,
    value_of_scaled_chunks hp inv q2.2.1 q3.2.1,
    value_of_scaled_chunks hp inv q0.1 q1.1,
    value_of_scaled_chunks hp inv q2.1 q3.1⟩

/-- The first four XOR queries force the 16-bit rotation in Clean's G function.
    Addition is connected to the input words separately; no honest witness
    generator is assumed. -/
theorem first_rotation {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) :
    let a : Word := ⟨(firstAlo w).val, (firstAhi w).val⟩
    let d : Word := ⟨(w 27).val, (w 28).val⟩
    let rotated : Word := ⟨(w 47).val + 256 * (w 48).val, (w 44).val + 256 * (w 45).val⟩
    a.Bounded ∧ d.Bounded ∧ rotated.Bounded ∧
      rotated.value = rotRight32 (d.value ^^^ a.value) 16 := by
  obtain ⟨q0, q1, q2, q3⟩ := first_xors hp compatible h
  obtain ⟨al, ah, dl, dh⟩ := first_byte_splits hp compatible h
  have low := xor_of_chunks (width := 8) q0.1 q0.2.1
    (a₁ := ((-7864320 : ZMod p) * (w 27 - w 43)).val)
    (b₁ := ((-7864320 : ZMod p) * (firstAlo w - w 41)).val)
  have high := xor_of_chunks (width := 8) q2.1 q2.2.1
    (a₁ := ((-7864320 : ZMod p) * (w 28 - w 46)).val)
    (b₁ := ((-7864320 : ZMod p) * (firstAhi w - w 42)).val)
  norm_num only [Nat.reducePow] at low high
  rw [← dl, ← al, ← q0.2.2.2, ← q1.2.2.2] at low
  rw [← dh, ← ah, ← q2.2.2.2, ← q3.2.2.2] at high
  have ab : (firstAlo w).val < 65536 ∧ (firstAhi w).val < 65536 := by
    have := q0.2.1; have := q1.2.1; have := q2.2.1; have := q3.2.1
    omega
  have db : (w 27).val < 65536 ∧ (w 28).val < 65536 := by
    have := q0.1; have := q1.1; have := q2.1; have := q3.1
    omega
  have rb : (w 47).val + 256 * (w 48).val < 65536 ∧
      (w 44).val + 256 * (w 45).val < 65536 := by
    have := q0.2.2.1; have := q1.2.2.1; have := q2.2.2.1; have := q3.2.2.1
    omega
  refine ⟨ab, db, rb, ?_⟩
  dsimp [Word.value, limbBase]
  have full := xor_of_chunks (width := 16) db.1 ab.1
    (a₁ := (w 28).val) (b₁ := (firstAhi w).val)
  norm_num only [Nat.reducePow] at full
  rw [full, low, high]
  have rotation := rotate_right_of_chunks (width := 16) (by decide) rb.2
    (high := (w 47).val + 256 * (w 48).val)
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [rotation]
  ring

/-- The first addition in Clean's G reference, recovered from the imported
    lookup chunks and Boolean carry constraints. Only input limb bounds are
    supplied by the memory interface. -/
theorem first_addition {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (leftBound : (Word.mk (w 15).val (w 16).val).Bounded)
    (rightBound : (Word.mk (w 19).val (w 20).val).Bounded)
    (messageBound : (Word.mk (w 33).val (w 34).val).Bounded) :
    (Word.mk (firstAlo w).val (firstAhi w).val).value =
      add32 (Word.mk (w 15).val (w 16).val).value
        (add32 (Word.mk (w 19).val (w 20).val).value
          (Word.mk (w 33).val (w 34).val).value) := by
  have outputBound := (first_rotation (by omega) compatible h).1
  have c0 := boolean_val (local_flags h 1)
  have c1 := boolean_val (local_flags h 2)
  have r0 := boolean_val (local_flags h 3)
  have r1 := boolean_val (local_flags h 4)
  simp [Variables.booleanColumns] at c0 c1 r0 r1
  have low : ((w 15).val : ZMod p) + (w 19).val + (w 33).val =
      (firstAlo w).val + 65536 * ((w 37).val + 2 * (w 38).val) := by
    simp only [ZMod.natCast_zmod_val]
    unfold firstAlo
    ring
  have high : (((w 37).val + 2 * (w 38).val : Nat) : ZMod p) +
      (w 16).val + (w 20).val + (w 34).val =
      (firstAhi w).val + 65536 * ((w 39).val + 2 * (w 40).val) := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    unfold firstAhi
    ring
  exact Word.add32_of_limbs hp
    (carry := (w 37).val + 2 * (w 38).val) (wrap := (w 39).val + 2 * (w 40).val)
    leftBound rightBound messageBound outputBound
    (by omega) (by omega)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using low)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using high)

end Airbender.Blake2G.Proofs
