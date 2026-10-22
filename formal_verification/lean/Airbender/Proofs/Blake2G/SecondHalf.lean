import Airbender.Proofs.Blake2G.AssemblyDefinitions
import Airbender.Proofs.Blake2G.Mixing

namespace Airbender.Blake2G.Proofs

open Arithmetic

set_option maxHeartbeats 1200000

private theorem second_xors_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    chunkXor 8 (w 47) (w 69) (w 71) ∧
    chunkXor 8 (w 48) ((-7864320 : ZMod p) * (secondAlo w - w 69)) (w 72) ∧
    chunkXor 8 (w 44) (w 70) (w 73) ∧
    chunkXor 8 (w 45) ((-7864320 : ZMod p) * (secondAhi w - w 70)) (w 74) := by
  have q10 := data_lookups_of_queries (by omega) h (10 : Fin 18)
  have q11 := data_lookups_of_queries (by omega) h (11 : Fin 18)
  have q12 := data_lookups_of_queries (by omega) h (12 : Fin 18)
  have q13 := data_lookups_of_queries (by omega) h (13 : Fin 18)
  simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment] at q10 q11 q12 q13
  have inv := inverse256 compatible
  have loQuery : -(7864320 * w 15) + -(7864320 * w 19) + -(7864320 * w 33) +
      -(7864320 * w 35) + -(256 * w 37) + -(512 * w 38) + -(7864320 * w 59) +
      -(125829120 * w 62) + -(1006632960 * w 63) + -(256 * w 65) + -(512 * w 66) +
      7864320 * w 69 = (-7864320 : ZMod p) * (secondAlo w - w 69) := by
    unfold secondAlo firstAlo
    linear_combination (256 * (w 37 + w 65) + 512 * (w 38 + w 66)) * inv
  have hiQuery : -(7864320 * w 16) + -(7864320 * w 20) + -(7864320 * w 34) +
      -(7864320 * w 36) + -(7864320 * w 37) + -(15728640 * w 38) + -(256 * w 39) + -(512 * w 40) +
      -(125829120 * w 57) + -(1006632960 * w 58) + -(7864320 * w 64) +
      -(7864320 * w 65) + -(15728640 * w 66) + -(256 * w 67) + -(512 * w 68) +
      7864320 * w 70 = (-7864320 : ZMod p) * (secondAhi w - w 70) := by
    unfold secondAhi firstAhi
    linear_combination (256 * (w 39 + w 67) + 512 * (w 40 + w 68)) * inv
  rw [loQuery] at q11
  rw [hiQuery] at q13
  exact ⟨q10, q11, q12, q13⟩

private theorem second_xors {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    chunkXor 8 (w 47) (w 69) (w 71) ∧
    chunkXor 8 (w 48) ((-7864320 : ZMod p) * (secondAlo w - w 69)) (w 72) ∧
    chunkXor 8 (w 44) (w 70) (w 73) ∧
    chunkXor 8 (w 45) ((-7864320 : ZMod p) * (secondAhi w - w 70)) (w 74) := by
  exact second_xors_of_queries hp compatible (query_holds_of_holds h)

/-- The second addition's byte decomposition follows from the actual queries. -/
theorem second_byte_splits_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    (secondAlo w).val = (w 69).val + 256 * ((-7864320 : ZMod p) * (secondAlo w - w 69)).val ∧
    (secondAhi w).val = (w 70).val + 256 * ((-7864320 : ZMod p) * (secondAhi w - w 70)).val := by
  obtain ⟨q10, q11, q12, q13⟩ := second_xors_of_queries hp compatible h
  have inv := inverse256 compatible
  exact ⟨value_of_scaled_chunks hp inv q10.2.1 q11.2.1,
    value_of_scaled_chunks hp inv q12.2.1 q13.2.1⟩

theorem second_byte_splits {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    (secondAlo w).val = (w 69).val + 256 * ((-7864320 : ZMod p) * (secondAlo w - w 69)).val ∧
    (secondAhi w).val = (w 70).val + 256 * ((-7864320 : ZMod p) * (secondAhi w - w 70)).val := by
  exact second_byte_splits_of_queries hp compatible (query_holds_of_holds h)

/-- The second four byte queries force Clean's XOR/rotate-8 operation. -/
theorem second_rotation_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    let a : Word := ⟨(secondAlo w).val, (secondAhi w).val⟩
    let d : Word := ⟨(w 47).val + 256 * (w 48).val, (w 44).val + 256 * (w 45).val⟩
    let rotated : Word := ⟨(w 72).val + 256 * (w 73).val, (w 74).val + 256 * (w 71).val⟩
    a.Bounded ∧ rotated.Bounded ∧ rotated.value = rotRight32 (d.value ^^^ a.value) 8 := by
  obtain ⟨q10, q11, q12, q13⟩ := second_xors_of_queries hp compatible h
  obtain ⟨al, ah⟩ := second_byte_splits_of_queries hp compatible h
  have low := xor_of_chunks (width := 8) q10.1 q10.2.1
    (a₁ := (w 48).val) (b₁ := ((-7864320 : ZMod p) * (secondAlo w - w 69)).val)
  have high := xor_of_chunks (width := 8) q12.1 q12.2.1
    (a₁ := (w 45).val) (b₁ := ((-7864320 : ZMod p) * (secondAhi w - w 70)).val)
  norm_num only [Nat.reducePow] at low high
  rw [← al, ← q10.2.2.2, ← q11.2.2.2] at low
  rw [← ah, ← q12.2.2.2, ← q13.2.2.2] at high
  have ab : (secondAlo w).val < 65536 ∧ (secondAhi w).val < 65536 := by
    have := q10.2.1; have := q11.2.1; have := q12.2.1; have := q13.2.1
    omega
  have rb : (w 72).val + 256 * (w 73).val < 65536 ∧
      (w 74).val + 256 * (w 71).val < 65536 := by
    have := q10.2.2.1; have := q11.2.2.1; have := q12.2.2.1; have := q13.2.2.1
    omega
  have db := (first_rotation_of_queries hp compatible h).2.2.1
  refine ⟨ab, rb, ?_⟩
  dsimp [Word.value, limbBase]
  have full := xor_of_chunks (width := 16) db.1 ab.1
    (a₁ := (w 44).val + 256 * (w 45).val) (b₁ := (secondAhi w).val)
  norm_num only [Nat.reducePow] at full
  rw [full, low, high]
  rw [show (w 71).val + 256 * (w 72).val + 65536 * ((w 73).val + 256 * (w 74).val) =
      (w 71).val + 256 * ((w 72).val + 256 * (w 73).val + 65536 * (w 74).val) by ring]
  have rotation := rotate_right_of_chunks (width := 8) (by decide) q10.2.2.1
    (high := (w 72).val + 256 * (w 73).val + 65536 * (w 74).val)
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [rotation]
  ring

theorem second_rotation {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    let a : Word := ⟨(secondAlo w).val, (secondAhi w).val⟩
    let d : Word := ⟨(w 47).val + 256 * (w 48).val, (w 44).val + 256 * (w 45).val⟩
    let rotated : Word := ⟨(w 72).val + 256 * (w 73).val, (w 74).val + 256 * (w 71).val⟩
    a.Bounded ∧ rotated.Bounded ∧ rotated.value = rotRight32 (d.value ^^^ a.value) 8 := by
  exact second_rotation_of_queries hp compatible (query_holds_of_holds h)

/-- The second a += b + message operation. Its inputs are the intermediates
    already recovered by the first-half proofs. -/
theorem second_addition {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control)))
    (messageBound : (Word.mk (w 35).val (w 36).val).Bounded) :
    (Word.mk (secondAlo w).val (secondAhi w).val).value =
      add32 (Word.mk (firstAlo w).val (firstAhi w).val).value
        (add32 (Word.mk ((w 59).val + 16 * (w 62).val + 128 * (w 63).val)
          ((w 64).val + 16 * (w 57).val + 128 * (w 58).val)).value
          (Word.mk (w 35).val (w 36).val).value) := by
  have leftBound := (first_rotation (by omega) compatible h).1
  have rightBound := (first_rotation12 (by omega) compatible h).2.2.1
  have outputBound := (second_rotation (by omega) compatible h).1
  have c0 := boolean_val (mixing_flags h 6)
  have c1 := boolean_val (mixing_flags h 7)
  have r0 := boolean_val (mixing_flags h 8)
  have r1 := boolean_val (mixing_flags h 9)
  simp [Variables.booleanColumns] at c0 c1 r0 r1
  have low : ((firstAlo w).val : ZMod p) +
      ((w 59).val + 16 * (w 62).val + 128 * (w 63).val : Nat) + (w 35).val =
      (secondAlo w).val + 65536 * ((w 65).val + 2 * (w 66).val : Nat) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    unfold secondAlo
    ring
  have high : (((w 65).val + 2 * (w 66).val : Nat) : ZMod p) + (firstAhi w).val +
      ((w 64).val + 16 * (w 57).val + 128 * (w 58).val : Nat) + (w 36).val =
      (secondAhi w).val + 65536 * ((w 67).val + 2 * (w 68).val : Nat) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    unfold secondAhi
    ring
  exact Word.add32_of_limbs hp
    (carry := (w 65).val + 2 * (w 66).val) (wrap := (w 67).val + 2 * (w 68).val)
    leftBound rightBound messageBound outputBound (by omega) (by omega) low high

private theorem inverse128 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    128 * (-15728640 : ZMod p) = 1 := by
  linear_combination compatible

private theorem second_b_xors_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    chunkXor 7 (w 59 + 16 * w 62) (w 77) (w 79) ∧
    chunkXor 9 (w 63) ((-15728640 : ZMod p) * (secondClo w - w 77)) (w 80) ∧
    chunkXor 7 (16 * w 57 + w 64) (w 78) (w 81) ∧
    chunkXor 9 (w 58) ((-15728640 : ZMod p) * (secondChi w - w 78)) (w 82) := by
  have q14 := data_lookups_of_queries (by omega) h (14 : Fin 18)
  have q15 := data_lookups_of_queries (by omega) h (15 : Fin 18)
  have q16 := data_lookups_of_queries (by omega) h (16 : Fin 18)
  have q17 := data_lookups_of_queries (by omega) h (17 : Fin 18)
  simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment] at q14 q15 q16 q17
  have inv := inverse128 compatible
  have loQuery : -(15728640 * w 23) + -(15728640 * w 47) + 2 * w 48 + -(512 * w 49) +
      -(15728640 * w 72) + 2 * w 73 + -(512 * w 75) + 15728640 * w 77 =
      (-15728640 : ZMod p) * (secondClo w - w 77) := by
    unfold secondClo firstClo
    linear_combination (512 * (w 49 + w 75) - 2 * (w 48 + w 73)) * inv
  have hiQuery : -(15728640 * w 24) + -(15728640 * w 44) + 2 * w 45 + -(15728640 * w 49) +
      -(512 * w 50) + 2 * w 71 + -(15728640 * w 74) + -(15728640 * w 75) +
      -(512 * w 76) + 15728640 * w 78 =
      (-15728640 : ZMod p) * (secondChi w - w 78) := by
    unfold secondChi firstChi
    linear_combination (512 * (w 50 + w 76) - 2 * (w 45 + w 71)) * inv
  rw [loQuery] at q15
  rw [hiQuery] at q17
  exact ⟨q14, q15, q16, q17⟩

private theorem second_b_xors {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    chunkXor 7 (w 59 + 16 * w 62) (w 77) (w 79) ∧
    chunkXor 9 (w 63) ((-15728640 : ZMod p) * (secondClo w - w 77)) (w 80) ∧
    chunkXor 7 (16 * w 57 + w 64) (w 78) (w 81) ∧
    chunkXor 9 (w 58) ((-15728640 : ZMod p) * (secondChi w - w 78)) (w 82) := by
  exact second_b_xors_of_queries hp compatible (query_holds_of_holds h)

/-- The final c word is ranged by the rotate-7 queries. -/
theorem second_c_splits_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    (secondClo w).val = (w 77).val + 128 * ((-15728640 : ZMod p) * (secondClo w - w 77)).val ∧
    (secondChi w).val = (w 78).val + 128 * ((-15728640 : ZMod p) * (secondChi w - w 78)).val := by
  obtain ⟨q14, q15, q16, q17⟩ := second_b_xors_of_queries hp compatible h
  have inv := inverse128 compatible
  exact ⟨value_of_scaled_chunks hp inv q14.2.1 q15.2.1,
    value_of_scaled_chunks hp inv q16.2.1 q17.2.1⟩

theorem second_c_splits {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    (secondClo w).val = (w 77).val + 128 * ((-15728640 : ZMod p) * (secondClo w - w 77)).val ∧
    (secondChi w).val = (w 78).val + 128 * ((-15728640 : ZMod p) * (secondChi w - w 78)).val := by
  exact second_c_splits_of_queries hp compatible (query_holds_of_holds h)

/-- The last four imported queries force Clean's XOR/rotate-7 operation. -/
theorem second_rotation7_of_queries {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
    let b : Word := ⟨(w 59).val + 16 * (w 62).val + 128 * (w 63).val,
      (w 64).val + 16 * (w 57).val + 128 * (w 58).val⟩
    let c : Word := ⟨(secondClo w).val, (secondChi w).val⟩
    let rotated : Word := ⟨(w 80).val + 512 * (w 81).val, (w 82).val + 512 * (w 79).val⟩
    c.Bounded ∧ rotated.Bounded ∧ rotated.value = rotRight32 (b.value ^^^ c.value) 7 := by
  obtain ⟨q14, q15, q16, q17⟩ := second_b_xors_of_queries hp compatible h
  obtain ⟨cl, ch⟩ := second_c_splits_of_queries hp compatible h
  have bb := (first_rotation12_of_queries hp compatible h).2.2.1
  change (w 59).val + 16 * (w 62).val + 128 * (w 63).val < 65536 ∧
    (w 64).val + 16 * (w 57).val + 128 * (w 58).val < 65536 at bb
  have bLoCast : (((w 59).val + 16 * (w 62).val : Nat) : ZMod p) = w 59 + 16 * w 62 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  have bHiCast : (((w 64).val + 16 * (w 57).val : Nat) : ZMod p) = 16 * w 57 + w 64 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    ring
  have bLoValue : (w 59 + 16 * w 62).val = (w 59).val + 16 * (w 62).val := by
    rw [← bLoCast]
    exact ZMod.val_natCast_of_lt (by have := bb.1; omega)
  have bHiValue : (16 * w 57 + w 64).val = (w 64).val + 16 * (w 57).val := by
    rw [← bHiCast]
    exact ZMod.val_natCast_of_lt (by have := bb.2; omega)
  have bLow : (w 59).val + 16 * (w 62).val < 2 ^ 7 := by simpa only [bLoValue] using q14.1
  have bHigh : (w 64).val + 16 * (w 57).val < 2 ^ 7 := by simpa only [bHiValue] using q16.1
  have loXor : (w 79).val = ((w 59).val + 16 * (w 62).val) ^^^ (w 77).val := by
    simpa only [bLoValue] using q14.2.2.2
  have hiXor : (w 81).val = ((w 64).val + 16 * (w 57).val) ^^^ (w 78).val := by
    simpa only [bHiValue] using q16.2.2.2
  have low := xor_of_chunks (width := 7) bLow q14.2.1
    (a₁ := (w 63).val) (b₁ := ((-15728640 : ZMod p) * (secondClo w - w 77)).val)
  have high := xor_of_chunks (width := 7) bHigh q16.2.1
    (a₁ := (w 58).val) (b₁ := ((-15728640 : ZMod p) * (secondChi w - w 78)).val)
  norm_num only [Nat.reducePow] at low high
  rw [← cl, ← loXor, ← q15.2.2.2] at low
  rw [← ch, ← hiXor, ← q17.2.2.2] at high
  have cb : (secondClo w).val < 65536 ∧ (secondChi w).val < 65536 := by
    have := q14.2.1; have := q15.2.1; have := q16.2.1; have := q17.2.1
    omega
  have rb : (w 80).val + 512 * (w 81).val < 65536 ∧
      (w 82).val + 512 * (w 79).val < 65536 := by
    have := q14.2.2.1; have := q15.2.2.1; have := q16.2.2.1; have := q17.2.2.1
    omega
  refine ⟨cb, rb, ?_⟩
  dsimp [Word.value, limbBase]
  have full := xor_of_chunks (width := 16) bb.1 cb.1
    (a₁ := (w 64).val + 16 * (w 57).val + 128 * (w 58).val) (b₁ := (secondChi w).val)
  norm_num only [Nat.reducePow] at full
  rw [full, low, high]
  rw [show (w 79).val + 128 * (w 80).val + 65536 * ((w 81).val + 128 * (w 82).val) =
      (w 79).val + 128 * ((w 80).val + 512 * (w 81).val + 65536 * (w 82).val) by ring]
  have rotation := rotate_right_of_chunks (width := 7) (by decide) q14.2.2.1
    (high := (w 80).val + 512 * (w 81).val + 65536 * (w 82).val)
  norm_num only [Nat.reduceSub, Nat.reducePow] at rotation
  rw [rotation]
  ring

theorem second_rotation7 {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    let b : Word := ⟨(w 59).val + 16 * (w 62).val + 128 * (w 63).val,
      (w 64).val + 16 * (w 57).val + 128 * (w 58).val⟩
    let c : Word := ⟨(secondClo w).val, (secondChi w).val⟩
    let rotated : Word := ⟨(w 80).val + 512 * (w 81).val, (w 82).val + 512 * (w 79).val⟩
    c.Bounded ∧ rotated.Bounded ∧ rotated.value = rotRight32 (b.value ^^^ c.value) 7 := by
  exact second_rotation7_of_queries hp compatible (query_holds_of_holds h)

/-- The final c += d addition, ranged by the last XOR queries. -/
theorem second_c_addition {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    (Word.mk (secondClo w).val (secondChi w).val).value =
      add32 (Word.mk (firstClo w).val (firstChi w).val).value
        (Word.mk ((w 72).val + 256 * (w 73).val) ((w 74).val + 256 * (w 71).val)).value := by
  have cBound := (first_rotation12 (by omega) compatible h).2.1
  have dBound := (second_rotation (by omega) compatible h).2.1
  have outputBound := (second_rotation7 (by omega) compatible h).1
  have carry := boolean_val (mixing_flags h 10)
  have wrap := boolean_val (mixing_flags h 11)
  simp [Variables.booleanColumns] at carry wrap
  have low : ((firstClo w).val : ZMod p) + ((w 72).val + 256 * (w 73).val : Nat) + 0 =
      (secondClo w).val + 65536 * (w 75).val := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    unfold secondClo
    ring
  have high : ((w 75).val : ZMod p) + (firstChi w).val +
      ((w 74).val + 256 * (w 71).val : Nat) + 0 =
      (secondChi w).val + 65536 * (w 76).val := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    unfold secondChi
    ring
  have result := Word.add32_of_limbs hp (carry := (w 75).val) (wrap := (w 76).val)
    cBound dBound (message := ⟨0, 0⟩) (by constructor <;> decide) outputBound
    (by omega) (by omega)
    (by simpa only [Nat.cast_zero] using low)
    (by simpa only [Nat.cast_zero] using high)
  have dValue := Word.value_lt dBound
  simpa [add32, show (2 : Nat) ^ 32 = wordModulus by rfl,
    Nat.mod_eq_of_lt dValue, Word.value, limbBase] using result

/-- All eight output limbs are tied to the recovered mixing intermediates by
    the imported zero assertions, not by a witness-generation equation. -/
theorem mixing_outputs {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    Word.mk (w 17).val (w 18).val = ⟨(secondAlo w).val, (secondAhi w).val⟩ ∧
    Word.mk (w 21).val (w 22).val = ⟨(w 80).val + 512 * (w 81).val, (w 82).val + 512 * (w 79).val⟩ ∧
    Word.mk (w 25).val (w 26).val = ⟨(secondClo w).val, (secondChi w).val⟩ ∧
    Word.mk (w 29).val (w 30).val = ⟨(w 72).val + 256 * (w 73).val, (w 74).val + 256 * (w 71).val⟩ := by
  have aLo := Verification.assertion_of_holds h ⟨0, by rw [mixing_constraint_count]; decide⟩
  have aHi := Verification.assertion_of_holds h ⟨1, by rw [mixing_constraint_count]; decide⟩
  have bLo := Verification.assertion_of_holds h ⟨2, by rw [mixing_constraint_count]; decide⟩
  have bHi := Verification.assertion_of_holds h ⟨3, by rw [mixing_constraint_count]; decide⟩
  have cLo := Verification.assertion_of_holds h ⟨4, by rw [mixing_constraint_count]; decide⟩
  have cHi := Verification.assertion_of_holds h ⟨5, by rw [mixing_constraint_count]; decide⟩
  have dLo := Verification.assertion_of_holds h ⟨6, by rw [mixing_constraint_count]; decide⟩
  have dHi := Verification.assertion_of_holds h ⟨7, by rw [mixing_constraint_count]; decide⟩
  simp [mixingConstraints, importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at aLo aHi bLo bHi cLo cHi dLo dHi
  have aLow : w 17 = secondAlo w := by unfold secondAlo firstAlo; linear_combination -aLo
  have aHigh : w 18 = secondAhi w := by unfold secondAhi firstAhi; linear_combination -aHi
  have cLow : w 25 = secondClo w := by unfold secondClo firstClo; linear_combination -cLo
  have cHigh : w 26 = secondChi w := by unfold secondChi firstChi; linear_combination -cHi
  have bLow : (((w 80).val + 512 * (w 81).val : Nat) : ZMod p) = w 21 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination bLo
  have bHigh : (((w 82).val + 512 * (w 79).val : Nat) : ZMod p) = w 22 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination bHi
  have dLow : (((w 72).val + 256 * (w 73).val : Nat) : ZMod p) = w 29 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination dLo
  have dHigh : (((w 74).val + 256 * (w 71).val : Nat) : ZMod p) = w 30 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination dHi
  have bb := (second_rotation7 hp compatible h).2.1
  have db := (second_rotation hp compatible h).2.1
  change (w 80).val + 512 * (w 81).val < 65536 ∧ (w 82).val + 512 * (w 79).val < 65536 at bb
  change (w 72).val + 256 * (w 73).val < 65536 ∧ (w 74).val + 256 * (w 71).val < 65536 at db
  refine ⟨by rw [aLow, aHigh], ?_, by rw [cLow, cHigh], ?_⟩
  · rw [Word.mk.injEq]
    constructor
    · rw [← bLow]; exact ZMod.val_natCast_of_lt (by have := bb.1; omega)
    · rw [← bHigh]; exact ZMod.val_natCast_of_lt (by have := bb.2; omega)
  · rw [Word.mk.injEq]
    constructor
    · rw [← dLow]; exact ZMod.val_natCast_of_lt (by have := db.1; omega)
    · rw [← dHigh]; exact ZMod.val_natCast_of_lt (by have := db.2; omega)

end Airbender.Blake2G.Proofs
