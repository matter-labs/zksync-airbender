import Airbender.Review.Circuits.Blake2Round.Finalization
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Proofs.Blake2Round.Lookups
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Proofs.Arithmetic.FieldChunks
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

open Arithmetic Blake2G.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Two native chunk XORs imply XOR of the canonical sixteen-bit limbs. -/
theorem xor_limb_chunks {p width remaining : Nat} [Fact p.Prime]
    (hp : 65536 ≤ p) (capacity : 2 ^ width * 2 ^ remaining = 65536)
    {x y z xl xh yl yh zl zh : ZMod p}
    (low : chunkXor width xl yl zl) (high : chunkXor remaining xh yh zh)
    (xChunks : x = xl + (2 ^ width : Nat) * xh)
    (yChunks : y = yl + (2 ^ width : Nat) * yh)
    (zChunks : z = zl + (2 ^ width : Nat) * zh) :
    x.val < 65536 ∧ y.val < 65536 ∧ z.val < 65536 ∧ z.val = x.val ^^^ y.val := by
  have bound : 2 ^ width * 2 ^ remaining ≤ p := by rw [capacity]; exact hp
  have xv := value_of_chunks bound low.1 high.1 xChunks
  have yv := value_of_chunks bound low.2.1 high.2.1 yChunks
  have zv := value_of_chunks bound low.2.2.1 high.2.2.1 zChunks
  have small {a b : Nat} (ha : a < 2 ^ width) (hb : b < 2 ^ remaining) :
      a + 2 ^ width * b < 65536 := by
    calc
      _ < 2 ^ width + 2 ^ width * b := Nat.add_lt_add_right ha _
      _ = 2 ^ width * (b + 1) := by ring
      _ ≤ 2 ^ width * 2 ^ remaining := Nat.mul_le_mul_left _ (by omega)
      _ = _ := capacity
  refine ⟨xv ▸ small low.1 high.1, yv ▸ small low.2.1 high.2.1,
    zv ▸ small low.2.2.1 high.2.2.1, ?_⟩
  rw [xv, yv, zv, xor_of_chunks low.1 low.2.1, low.2.2.2, high.2.2.2]

-- These are projections of the actual imported queries, not a second model.
def finalQuery {p : Nat} [Fact p.Prime] (limb : Fin 16) (stage : Fin 4) : Lookup (ZMod p) :=
  (FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨146 + 4 * limb.val + stage.val, by
      rw [lookup_count]; have := limb.isLt; have := stage.isLt; omega⟩

def finalColumn {p : Nat} [Fact p.Prime] (w : Nat → ZMod p)
    (limb : Fin 16) (stage column : Fin 4) : ZMod p :=
  ((finalQuery limb stage).entry.toArray[column.val]!).eval (Verification.environment w)

theorem final_query {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {w : Nat → ZMod p} (limb : Fin 16) (stage : Fin 4) (kind : Fin 5)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (tag : finalColumn w limb stage 3 = ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p)) :
    chunkXor (#v[8, 3, 4, 7, 9][kind])
      (finalColumn w limb stage 0) (finalColumn w limb stage 1)
      (finalColumn w limb stage 2) := by
  have member := Verification.lookup_of_holds h
    ⟨146 + 4 * limb.val + stage.val, by
      rw [lookup_count]; have := limb.isLt; have := stage.isLt; omega⟩
  have table : (finalQuery (p := p) limb stage).table = setupTable.toRaw := by
    fin_cases limb <;> fin_cases stage <;> rfl
  exact xor_lookup_raw hp kind member table tag

def acInitial {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (154 + 4 * (limb.val / 2) + 2 * (limb.val % 2))

def acA {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (39 + 4 * (limb.val / 2) + limb.val % 2)

def acC {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (71 + 4 * (limb.val / 2) + limb.val % 2)

def acLowC : Vector Nat 8 := #v[578, 579, 622, 623, 490, 491, 534, 535]

set_option maxHeartbeats 16000000 in
/-- The first four chaining words use seven/nine-bit XOR queries. The write
    equations identify their inputs with the allocated final a/c state limbs. -/
theorem ac_queries {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (w (628 + 7 * limb.val)) (w acLowC[limb]) (w (629 + 7 * limb.val)) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w limb - w (628 + 7 * limb.val)))
      ((-15728640 : ZMod p) * (acC w limb - w acLowC[limb])) (w (630 + 7 * limb.val)) ∧
    chunkXor 7 (w (629 + 7 * limb.val)) (w (631 + 7 * limb.val)) (w (633 + 7 * limb.val)) ∧
    chunkXor 9 (w (630 + 7 * limb.val))
      ((-15728640 : ZMod p) * (acA w limb - w (631 + 7 * limb.val)))
      (w (634 + 7 * limb.val)) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w (limb.castLE (by omega)) stage 3 =
      (if stage.val % 2 = 0 then 19 else 20 : ZMod 2013265921) := by
    fin_cases limb <;> fin_cases stage <;> simp [finalColumn, finalQuery,
      importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) (limb.castLE (by omega)) 0 3 h (tag 0)
  have q1 := final_query (by decide) (limb.castLE (by omega)) 1 4 h (tag 1)
  have q2 := final_query (by decide) (limb.castLE (by omega)) 2 3 h (tag 2)
  have q3 := final_query (by decide) (limb.castLE (by omega)) 3 4 h (tag 3)
  have cWrite := Verification.assertion_of_holds h
    ⟨136 + 2 * (limb.val / 2) + limb.val % 2, by rw [constraint_count]; have := limb.isLt; omega⟩
  have aWrite := Verification.assertion_of_holds h
    ⟨120 + 2 * (limb.val / 2) + limb.val % 2, by rw [constraint_count]; have := limb.isLt; omega⟩
  have split := Verification.assertion_of_holds h
    ⟨152 + 2 * limb.val, by rw [constraint_count]; have := limb.isLt; omega⟩
  have cHigh : finalColumn w (limb.castLE (by omega)) 1 1 =
      (-15728640 : ZMod 2013265921) * (acC w limb - w acLowC[limb]) := by
    fin_cases limb
    all_goals simp [finalColumn, finalQuery, importedConstraints, FlatOperation.lookups,
      FlatOperation.constraints, Expression.eval, Verification.environment, acC, acLowC] at cWrite ⊢
    all_goals linear_combination (norm := ring_nf) (-15728640 : ZMod 2013265921) * cWrite
    all_goals reduce_mod_char
  have aHigh : finalColumn w (limb.castLE (by omega)) 3 1 =
      (-15728640 : ZMod 2013265921) * (acA w limb - w (631 + 7 * limb.val)) := by
    fin_cases limb
    all_goals simp [finalColumn, finalQuery, importedConstraints, FlatOperation.lookups,
      FlatOperation.constraints, Expression.eval, Verification.environment, acA] at aWrite split ⊢
    all_goals linear_combination (norm := ring_nf) (-15728640 : ZMod 2013265921) * (aWrite - split)
    all_goals reduce_mod_char
  have initialHigh : finalColumn w (limb.castLE (by omega)) 1 0 =
      (-15728640 : ZMod 2013265921) * (acInitial w limb - w (628 + 7 * limb.val)) := by
    fin_cases limb
    all_goals simp [finalColumn, finalQuery, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acInitial]
    all_goals ring
  rw [initialHigh, cHigh] at q1
  rw [aHigh] at q3
  fin_cases limb
  all_goals simp [finalColumn, finalQuery, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, acInitial, acC, acA, acLowC] at q0 q1 q2 q3 ⊢
  all_goals exact ⟨q0, q1, q2, q3⟩

end Airbender.Blake2Round.Proofs
