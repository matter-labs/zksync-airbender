import Airbender.Proofs.Blake2G.SerializedField
import Airbender.Proofs.Blake2G.AssemblyDefinitions
import Airbender.Proofs.Blake2G
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Blake2G.Proofs

open Arithmetic

set_option maxHeartbeats 1200000

-- These are intermediate field expressions from the imported queries, not a
-- second G specification. The target operation is Clean's native reference.
def chunkXor {p : Nat} (width : Nat) (x y z : ZMod p) : Prop :=
  x.val < 2 ^ width ∧ y.val < 2 ^ width ∧ z.val < 2 ^ width ∧ z.val = x.val ^^^ y.val

private theorem first_xors_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    chunkXor 8 (w 43) (w 41) (w 44) ∧
    chunkXor 8 ((-7864320 : ZMod p) * (w 27 - w 43))
      ((-7864320 : ZMod p) * (firstAlo w - w 41)) (w 45) ∧
    chunkXor 8 (w 46) (w 42) (w 47) ∧
    chunkXor 8 ((-7864320 : ZMod p) * (w 28 - w 46))
      ((-7864320 : ZMod p) * (firstAhi w - w 42)) (w 48) := by
  have q0 := data_lookups_of_queries (by omega) h (0 : Fin 18)
  have q1 := data_lookups_of_queries (by omega) h (1 : Fin 18)
  have q2 := data_lookups_of_queries (by omega) h (2 : Fin 18)
  have q3 := data_lookups_of_queries (by omega) h (3 : Fin 18)
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

private theorem first_xors {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    chunkXor 8 (w 43) (w 41) (w 44) ∧
    chunkXor 8 ((-7864320 : ZMod p) * (w 27 - w 43))
      ((-7864320 : ZMod p) * (firstAlo w - w 41)) (w 45) ∧
    chunkXor 8 (w 46) (w 42) (w 47) ∧
    chunkXor 8 ((-7864320 : ZMod p) * (w 28 - w 46))
      ((-7864320 : ZMod p) * (firstAhi w - w 42)) (w 48) := by
  exact first_xors_of_queries hp compatible (query_holds_of_holds h)

/-- Recover the byte splits of the first addition and the incoming d word from
    the four actual imported XOR queries. -/
theorem first_byte_splits_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    (firstAlo w).val = (w 41).val + 256 * ((-7864320 : ZMod p) * (firstAlo w - w 41)).val ∧
    (firstAhi w).val = (w 42).val + 256 * ((-7864320 : ZMod p) * (firstAhi w - w 42)).val ∧
    (w 27).val = (w 43).val + 256 * ((-7864320 : ZMod p) * (w 27 - w 43)).val ∧
    (w 28).val = (w 46).val + 256 * ((-7864320 : ZMod p) * (w 28 - w 46)).val := by
  obtain ⟨q0, q1, q2, q3⟩ := first_xors_of_queries hp compatible h
  have inv := inverse256 compatible
  exact ⟨value_of_scaled_chunks hp inv q0.2.1 q1.2.1,
    value_of_scaled_chunks hp inv q2.2.1 q3.2.1,
    value_of_scaled_chunks hp inv q0.1 q1.1,
    value_of_scaled_chunks hp inv q2.1 q3.1⟩

theorem first_byte_splits {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    (firstAlo w).val = (w 41).val + 256 * ((-7864320 : ZMod p) * (firstAlo w - w 41)).val ∧
    (firstAhi w).val = (w 42).val + 256 * ((-7864320 : ZMod p) * (firstAhi w - w 42)).val ∧
    (w 27).val = (w 43).val + 256 * ((-7864320 : ZMod p) * (w 27 - w 43)).val ∧
    (w 28).val = (w 46).val + 256 * ((-7864320 : ZMod p) * (w 28 - w 46)).val := by
  exact first_byte_splits_of_queries hp compatible (query_holds_of_holds h)

/-- The first four XOR queries force the 16-bit rotation in Clean's G function.
    Addition is connected to the input words separately; no honest witness
    generator is assumed. -/
theorem first_rotation_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    let a : Word := ⟨(firstAlo w).val, (firstAhi w).val⟩
    let d : Word := ⟨(w 27).val, (w 28).val⟩
    let rotated : Word := ⟨(w 47).val + 256 * (w 48).val, (w 44).val + 256 * (w 45).val⟩
    a.Bounded ∧ d.Bounded ∧ rotated.Bounded ∧
      rotated.value = rotRight32 (d.value ^^^ a.value) 16 := by
  obtain ⟨q0, q1, q2, q3⟩ := first_xors_of_queries hp compatible h
  obtain ⟨al, ah, dl, dh⟩ := first_byte_splits_of_queries hp compatible h
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

theorem first_rotation {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    let a : Word := ⟨(firstAlo w).val, (firstAhi w).val⟩
    let d : Word := ⟨(w 27).val, (w 28).val⟩
    let rotated : Word := ⟨(w 47).val + 256 * (w 48).val, (w 44).val + 256 * (w 45).val⟩
    a.Bounded ∧ d.Bounded ∧ rotated.Bounded ∧
      rotated.value = rotRight32 (d.value ^^^ a.value) 16 := by
  exact first_rotation_of_queries hp compatible (query_holds_of_holds h)

private theorem inverse4096 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    4096 * (-491520 : ZMod p) = 1 := by
  linear_combination compatible

private theorem first_b_xors_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    chunkXor 3 (w 55) (w 51) (w 57) ∧
    chunkXor 9 (w 56) (w 52) (w 58) ∧
    chunkXor 4 ((-491520 : ZMod p) * (w 19 - (w 55 + 8 * w 56)))
      ((-491520 : ZMod p) * (firstClo w - (w 51 + 8 * w 52))) (w 59) ∧
    chunkXor 3 (w 60) (w 53) (w 62) ∧
    chunkXor 9 (w 61) (w 54) (w 63) ∧
    chunkXor 4 ((-491520 : ZMod p) * (w 20 - (w 60 + 8 * w 61)))
      ((-491520 : ZMod p) * (firstChi w - (w 53 + 8 * w 54))) (w 64) := by
  have q4 := data_lookups_of_queries (by omega) h (4 : Fin 18)
  have q5 := data_lookups_of_queries (by omega) h (5 : Fin 18)
  have q6 := data_lookups_of_queries (by omega) h (6 : Fin 18)
  have q7 := data_lookups_of_queries (by omega) h (7 : Fin 18)
  have q8 := data_lookups_of_queries (by omega) h (8 : Fin 18)
  have q9 := data_lookups_of_queries (by omega) h (9 : Fin 18)
  simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment] at q4 q5 q6 q7 q8 q9
  have inv := inverse4096 compatible
  have bLo : -(491520 * w 19) + 491520 * w 55 + 3932160 * w 56 =
      (-491520 : ZMod p) * (w 19 - (w 55 + 8 * w 56)) := by ring
  have bHi : -(491520 * w 20) + 491520 * w 60 + 3932160 * w 61 =
      (-491520 : ZMod p) * (w 20 - (w 60 + 8 * w 61)) := by ring
  have cLo : -(491520 * w 23) + -(491520 * w 47) + -(125829120 * w 48) +
      -(16 * w 49) + 491520 * w 51 + 3932160 * w 52 =
      (-491520 : ZMod p) * (firstClo w - (w 51 + 8 * w 52)) := by
    unfold firstClo
    linear_combination (16 * w 49) * inv
  have cHi : -(491520 * w 24) + -(491520 * w 44) + -(125829120 * w 45) +
      -(491520 * w 49) + -(16 * w 50) + 491520 * w 53 + 3932160 * w 54 =
      (-491520 : ZMod p) * (firstChi w - (w 53 + 8 * w 54)) := by
    unfold firstChi
    linear_combination (16 * w 50) * inv
  rw [bLo, cLo] at q6
  rw [bHi, cHi] at q9
  exact ⟨q4, q5, q6, q7, q8, q9⟩

private theorem first_b_xors {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    chunkXor 3 (w 55) (w 51) (w 57) ∧
    chunkXor 9 (w 56) (w 52) (w 58) ∧
    chunkXor 4 ((-491520 : ZMod p) * (w 19 - (w 55 + 8 * w 56)))
      ((-491520 : ZMod p) * (firstClo w - (w 51 + 8 * w 52))) (w 59) ∧
    chunkXor 3 (w 60) (w 53) (w 62) ∧
    chunkXor 9 (w 61) (w 54) (w 63) ∧
    chunkXor 4 ((-491520 : ZMod p) * (w 20 - (w 60 + 8 * w 61)))
      ((-491520 : ZMod p) * (firstChi w - (w 53 + 8 * w 54))) (w 64) := by
  exact first_b_xors_of_queries hp compatible (query_holds_of_holds h)

/-- The 3/9/4-bit lookup chunks reconstruct both inputs to the rotate-12 stage. -/
theorem first_middle_splits_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    (w 19).val = (w 55).val + 8 * (w 56).val + 4096 *
      ((-491520 : ZMod p) * (w 19 - (w 55 + 8 * w 56))).val ∧
    (w 20).val = (w 60).val + 8 * (w 61).val + 4096 *
      ((-491520 : ZMod p) * (w 20 - (w 60 + 8 * w 61))).val ∧
    (firstClo w).val = (w 51).val + 8 * (w 52).val + 4096 *
      ((-491520 : ZMod p) * (firstClo w - (w 51 + 8 * w 52))).val ∧
    (firstChi w).val = (w 53).val + 8 * (w 54).val + 4096 *
      ((-491520 : ZMod p) * (firstChi w - (w 53 + 8 * w 54))).val := by
  obtain ⟨q4, q5, q6, q7, q8, q9⟩ := first_b_xors_of_queries hp compatible h
  have inv := inverse4096 compatible
  exact ⟨value_of_three_chunks (lowRadix := 8) (middleRadix := 512) hp inv q4.1 q5.1 q6.1,
    value_of_three_chunks (lowRadix := 8) (middleRadix := 512) hp inv q7.1 q8.1 q9.1,
    value_of_three_chunks (lowRadix := 8) (middleRadix := 512) hp inv q4.2.1 q5.2.1 q6.2.1,
    value_of_three_chunks (lowRadix := 8) (middleRadix := 512) hp inv q7.2.1 q8.2.1 q9.2.1⟩

theorem first_middle_splits {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    (w 19).val = (w 55).val + 8 * (w 56).val + 4096 *
      ((-491520 : ZMod p) * (w 19 - (w 55 + 8 * w 56))).val ∧
    (w 20).val = (w 60).val + 8 * (w 61).val + 4096 *
      ((-491520 : ZMod p) * (w 20 - (w 60 + 8 * w 61))).val ∧
    (firstClo w).val = (w 51).val + 8 * (w 52).val + 4096 *
      ((-491520 : ZMod p) * (firstClo w - (w 51 + 8 * w 52))).val ∧
    (firstChi w).val = (w 53).val + 8 * (w 54).val + 4096 *
      ((-491520 : ZMod p) * (firstChi w - (w 53 + 8 * w 54))).val := by
  exact first_middle_splits_of_queries hp compatible (query_holds_of_holds h)

/-- The six mixed-width queries force the second XOR/rotation in Clean's G.
    They also range-check the incoming b word and the intermediate c word. -/
theorem first_rotation12_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    let b : Word := ⟨(w 19).val, (w 20).val⟩
    let c : Word := ⟨(firstClo w).val, (firstChi w).val⟩
    let rotated : Word := ⟨(w 59).val + 16 * (w 62).val + 128 * (w 63).val,
      (w 64).val + 16 * (w 57).val + 128 * (w 58).val⟩
    b.Bounded ∧ c.Bounded ∧ rotated.Bounded ∧
      rotated.value = rotRight32 (b.value ^^^ c.value) 12 := by
  obtain ⟨q4, q5, q6, q7, q8, q9⟩ := first_b_xors_of_queries hp compatible h
  obtain ⟨bl, bh, cl, ch⟩ := first_middle_splits_of_queries hp compatible h
  have bLow : (w 55).val + 8 * (w 56).val < 4096 := by
    have := q4.1; have := q5.1; omega
  have cLow : (w 51).val + 8 * (w 52).val < 4096 := by
    have := q4.2.1; have := q5.2.1; omega
  have bHigh : (w 60).val + 8 * (w 61).val < 4096 := by
    have := q7.1; have := q8.1; omega
  have cHigh : (w 53).val + 8 * (w 54).val < 4096 := by
    have := q7.2.1; have := q8.2.1; omega
  have blockLow := xor_of_chunks (width := 3) q4.1 q4.2.1
    (a₁ := (w 56).val) (b₁ := (w 52).val)
  have blockHigh := xor_of_chunks (width := 3) q7.1 q7.2.1
    (a₁ := (w 61).val) (b₁ := (w 54).val)
  norm_num only [Nat.reducePow] at blockLow blockHigh
  rw [← q4.2.2.2, ← q5.2.2.2] at blockLow
  rw [← q7.2.2.2, ← q8.2.2.2] at blockHigh
  have low := xor_of_chunks (width := 12) bLow cLow
    (a₁ := ((-491520 : ZMod p) * (w 19 - (w 55 + 8 * w 56))).val)
    (b₁ := ((-491520 : ZMod p) * (firstClo w - (w 51 + 8 * w 52))).val)
  have high := xor_of_chunks (width := 12) bHigh cHigh
    (a₁ := ((-491520 : ZMod p) * (w 20 - (w 60 + 8 * w 61))).val)
    (b₁ := ((-491520 : ZMod p) * (firstChi w - (w 53 + 8 * w 54))).val)
  norm_num only [Nat.reducePow] at low high
  rw [← bl, ← cl, blockLow, ← q6.2.2.2] at low
  rw [← bh, ← ch, blockHigh, ← q9.2.2.2] at high
  have bb : (w 19).val < 65536 ∧ (w 20).val < 65536 := by
    have := q6.1; have := q9.1; omega
  have cb : (firstClo w).val < 65536 ∧ (firstChi w).val < 65536 := by
    have := q6.2.1; have := q9.2.1; omega
  have rb : (w 59).val + 16 * (w 62).val + 128 * (w 63).val < 65536 ∧
      (w 64).val + 16 * (w 57).val + 128 * (w 58).val < 65536 := by
    have := q4.2.2.1; have := q5.2.2.1; have := q6.2.2.1
    have := q7.2.2.1; have := q8.2.2.1; have := q9.2.2.1
    omega
  have xorLowBound : (w 57).val + 8 * (w 58).val < 4096 := by
    have := q4.2.2.1; have := q5.2.2.1; omega
  refine ⟨bb, cb, rb, ?_⟩
  dsimp [Word.value, limbBase]
  have full := xor_of_chunks (width := 16) bb.1 cb.1
    (a₁ := (w 20).val) (b₁ := (firstChi w).val)
  norm_num only [Nat.reducePow] at full
  rw [full, low, high]
  rw [show (w 57).val + 8 * (w 58).val + 4096 * (w 59).val +
      65536 * ((w 62).val + 8 * (w 63).val + 4096 * (w 64).val) =
      ((w 57).val + 8 * (w 58).val) +
        4096 * ((w 59).val + 16 * (w 62).val + 128 * (w 63).val + 65536 * (w 64).val) by ring]
  have rotation := rotate_right_of_chunks (width := 12) (by decide) xorLowBound
    (high := (w 59).val + 16 * (w 62).val + 128 * (w 63).val + 65536 * (w 64).val)
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [rotation]
  ring

theorem first_rotation12 {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    let b : Word := ⟨(w 19).val, (w 20).val⟩
    let c : Word := ⟨(firstClo w).val, (firstChi w).val⟩
    let rotated : Word := ⟨(w 59).val + 16 * (w 62).val + 128 * (w 63).val,
      (w 64).val + 16 * (w 57).val + 128 * (w 58).val⟩
    b.Bounded ∧ c.Bounded ∧ rotated.Bounded ∧
      rotated.value = rotRight32 (b.value ^^^ c.value) 12 := by
  exact first_rotation12_of_queries hp compatible (query_holds_of_holds h)

/-- The c += d addition of the first half-round, using the c bounds recovered
    from the rotate-12 queries and d bounds from the rotate-16 queries. -/
theorem first_c_addition {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control)))
    (inputBound : (Word.mk (w 23).val (w 24).val).Bounded) :
    (Word.mk (firstClo w).val (firstChi w).val).value =
      add32 (Word.mk (w 23).val (w 24).val).value
        (Word.mk ((w 47).val + 256 * (w 48).val) ((w 44).val + 256 * (w 45).val)).value := by
  have dBound := (first_rotation (by omega) compatible h).2.2.1
  have cBound := (first_rotation12 (by omega) compatible h).2.1
  have carry := boolean_val (mixing_flags h 4)
  have wrap := boolean_val (mixing_flags h 5)
  simp [Variables.booleanColumns] at carry wrap
  have low : ((w 23).val : ZMod p) + ((w 47).val + 256 * (w 48).val : Nat) + 0 =
      (firstClo w).val + 65536 * (w 49).val := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    unfold firstClo
    ring
  have high : ((w 49).val : ZMod p) + (w 24).val +
      ((w 44).val + 256 * (w 45).val : Nat) + 0 =
      (firstChi w).val + 65536 * (w 50).val := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    unfold firstChi
    ring
  have result := Word.add32_of_limbs hp (carry := (w 49).val) (wrap := (w 50).val)
    inputBound dBound (message := ⟨0, 0⟩) (by constructor <;> decide) cBound
    (by omega) (by omega)
    (by simpa only [Nat.cast_zero] using low)
    (by simpa only [Nat.cast_zero] using high)
  have dValue := Word.value_lt dBound
  simpa [add32, show (2 : Nat) ^ 32 = wordModulus by rfl,
    Nat.mod_eq_of_lt dValue, Word.value, limbBase] using result

/-- The first addition in Clean's G reference, recovered from the imported
    lookup chunks and Boolean carry constraints. The b bounds come from the
    rotate-12 queries; a and message bounds remain memory interfaces. -/
theorem first_addition {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control)))
    (leftBound : (Word.mk (w 15).val (w 16).val).Bounded)
    (messageBound : (Word.mk (w 33).val (w 34).val).Bounded) :
    (Word.mk (firstAlo w).val (firstAhi w).val).value =
      add32 (Word.mk (w 15).val (w 16).val).value
        (add32 (Word.mk (w 19).val (w 20).val).value
          (Word.mk (w 33).val (w 34).val).value) := by
  have rightBound := (first_rotation12 (by omega) compatible h).1
  have outputBound := (first_rotation (by omega) compatible h).1
  have c0 := boolean_val (mixing_flags h 0)
  have c1 := boolean_val (mixing_flags h 1)
  have r0 := boolean_val (mixing_flags h 2)
  have r1 := boolean_val (mixing_flags h 3)
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
