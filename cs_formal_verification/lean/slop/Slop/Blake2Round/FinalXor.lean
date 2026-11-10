module
public import Human.Circuits.Blake2Round.Finalization
public import Slop.Blake2Round.ArtifactChecks
public import Slop.Blake2Round.Lookups
public import Slop.Blake2Round.OpIndex
public import Slop.Blake2G.Soundness
public import Slop.Arithmetic.FieldChunks
public import Mathlib.Tactic.ReduceModChar
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

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

/-- The final XOR is the last 64 fixed-table queries (imported lookups 130..193),
    four per sixteen-bit limb of the eight chaining writes. These are projections
    of the actual imported queries, not a second model. -/
noncomputable def finalQuery {p : Nat} [Fact p.Prime] (limb : Fin 16) (stage : Fin 4) :
    Lookup (ZMod p) :=
  (FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨128 + 4 * limb.val + stage.val + 2, by
      rw [lookup_count]; have := limb.isLt; have := stage.isLt; omega⟩

noncomputable def finalColumn {p : Nat} [Fact p.Prime] (w : Nat → ZMod p)
    (limb : Fin 16) (stage : Fin 4) (column : Fin 6) : ZMod p :=
  ((finalQuery limb stage).entry.toArray[column.val]!).eval (Verification.environment w)

private theorem get_mem_drop {α : Type} (l : List α) (k : Nat) (hk : k + 2 < l.length) :
    l.get ⟨k + 2, hk⟩ ∈ l.drop 2 :=
  List.mem_iff_getElem.mpr ⟨k, by rw [List.length_drop]; omega, by
    simp only [List.getElem_drop, List.get_eq_getElem]; congr 1; omega⟩

/-- A plain-XOR fixed-table query (tags 4, 19, 20: widths 8, 7, 9) is a chunk XOR
    of its first three columns. -/
theorem final_query {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {w : Nat → ZMod p} (limb : Fin 16) (stage : Fin 4) (kind : Fin 3)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (tag : finalColumn w limb stage 5 = ((#v[4, 19, 20][kind] : Nat) : ZMod p)) :
    chunkXor (#v[8, 7, 9][kind])
      (finalColumn w limb stage 0) (finalColumn w limb stage 1)
      (finalColumn w limb stage 2) := by
  have present : finalQuery (p := p) limb stage ∈
      (FlatOperation.lookups (importedConstraints setupTable)).drop 2 :=
    get_mem_drop _ _ _
  have member : #v[4, 19, 20][kind] ∈ tags := by
    fin_cases kind <;> simp [tags]
  have facts := data_lookups hp h _ present _ member tag
  change RowFacts _ (finalColumn w limb stage 0).val (finalColumn w limb stage 1).val
    (finalColumn w limb stage 2).val (finalColumn w limb stage 3).val
    (finalColumn w limb stage 4).val at facts
  fin_cases kind
  all_goals simp only [RowFacts, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    at facts ⊢
  all_goals obtain ⟨x, y, z, -, -⟩ := facts
  all_goals refine ⟨by norm_num; omega, by norm_num; omega, ?_, z⟩
  all_goals rw [z]
  all_goals exact Nat.xor_lt_two_pow (by norm_num; omega) (by norm_num; omega)

/-- Normalize a BabyBear field identity whose coefficients are serialized inverses. -/
macro "babybear_ring" : tactic => `(tactic| (
  ring_nf
  try reduce_mod_char
  try ring_nf
  try reduce_mod_char))

def acInitial {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (154 + 4 * (limb.val / 2) + 2 * (limb.val % 2))

def acA {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (39 + 4 * (limb.val / 2) + limb.val % 2)

def acC {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (71 + 4 * (limb.val / 2) + limb.val % 2)

/-- Shape of the four a/c queries of one limb (words 0..3): a 7/9-bit XOR of the
    chaining limb with c, then of that result with a. The serialized inverse of
    128 recombines each split, whatever low chunk the witness chooses. -/
theorem ac_shape {p : Nat} [Fact p.Prime] (field : p = 2013265921) (limb : Fin 8)
    (w : Nat → ZMod p) :
    finalColumn w (limb.castLE (by omega)) 0 5 = 19 ∧
    finalColumn w (limb.castLE (by omega)) 1 5 = 20 ∧
    finalColumn w (limb.castLE (by omega)) 2 5 = 19 ∧
    finalColumn w (limb.castLE (by omega)) 3 5 = 20 ∧
    acInitial w limb = finalColumn w (limb.castLE (by omega)) 0 0 +
      128 * finalColumn w (limb.castLE (by omega)) 1 0 ∧
    acC w limb = finalColumn w (limb.castLE (by omega)) 0 1 +
      128 * finalColumn w (limb.castLE (by omega)) 1 1 ∧
    finalColumn w (limb.castLE (by omega)) 2 0 = finalColumn w (limb.castLE (by omega)) 0 2 ∧
    finalColumn w (limb.castLE (by omega)) 3 0 = finalColumn w (limb.castLE (by omega)) 1 2 ∧
    acA w limb = finalColumn w (limb.castLE (by omega)) 2 1 +
      128 * finalColumn w (limb.castLE (by omega)) 3 1 := by
  subst field
  fin_cases limb
  all_goals simp only [finalColumn, finalQuery, Fin.val_castLE, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Fin.isValue, Fin.val_mk,
    Nat.reduceMul, Nat.reduceAdd]
  all_goals op_index
  all_goals simp [Expression.eval, Verification.environment, acInitial, acA, acC]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals babybear_ring

def bdInitial {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (170 + 4 * (limb.val / 2) + 2 * (limb.val % 2))
def bdB {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (55 + 4 * (limb.val / 2) + limb.val % 2)
def bdD {p : Nat} (w : Nat → ZMod p) (limb : Fin 8) : ZMod p :=
  w (87 + 4 * (limb.val / 2) + limb.val % 2)

/-- Shape of the four b/d queries of one limb (words 4..7): a 9/7-bit XOR of b with
    the chaining limb, re-split into 8/8 bits by the imported query expressions,
    then an 8/8-bit XOR with d. -/
theorem bd_shape {p : Nat} [Fact p.Prime] (field : p = 2013265921) (limb : Fin 8)
    (w : Nat → ZMod p) :
    finalColumn w ⟨8 + limb.val, by omega⟩ 0 5 = 20 ∧
    finalColumn w ⟨8 + limb.val, by omega⟩ 1 5 = 19 ∧
    finalColumn w ⟨8 + limb.val, by omega⟩ 2 5 = 4 ∧
    finalColumn w ⟨8 + limb.val, by omega⟩ 3 5 = 4 ∧
    bdB w limb = finalColumn w ⟨8 + limb.val, by omega⟩ 0 0 +
      512 * finalColumn w ⟨8 + limb.val, by omega⟩ 1 0 ∧
    bdInitial w limb = finalColumn w ⟨8 + limb.val, by omega⟩ 0 1 +
      512 * finalColumn w ⟨8 + limb.val, by omega⟩ 1 1 ∧
    finalColumn w ⟨8 + limb.val, by omega⟩ 0 2 +
      512 * finalColumn w ⟨8 + limb.val, by omega⟩ 1 2 =
      finalColumn w ⟨8 + limb.val, by omega⟩ 2 1 +
      256 * finalColumn w ⟨8 + limb.val, by omega⟩ 3 1 ∧
    bdD w limb = finalColumn w ⟨8 + limb.val, by omega⟩ 2 0 +
      256 * finalColumn w ⟨8 + limb.val, by omega⟩ 3 0 := by
  subst field
  fin_cases limb
  all_goals simp only [finalColumn, finalQuery, Fin.coe_ofNat_eq_mod,
    Nat.reduceMod, Fin.isValue, Fin.val_mk,
    Nat.reduceMul, Nat.reduceAdd]
  all_goals op_index
  all_goals simp [Expression.eval, Verification.environment, bdInitial, bdB, bdD]
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals babybear_ring

end Airbender.Blake2Round.Proofs
