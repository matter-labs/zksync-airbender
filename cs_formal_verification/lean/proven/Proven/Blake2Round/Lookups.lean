module
public import Human.Circuits.Blake2Round.Tables.Setup
public import Human.Circuits.Blake2Round.Artifact
public import Human.Helpers.Properties
public import Proven.Blake2Round.Setup.Rows
public import Proven.Constraints
public import Mathlib.Tactic.IntervalCases
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Blake2Round.Proofs

open SetupProofs

set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Meaning of one six-column setup row with tag `t`, columns `a b c d e`:
    plain XOR (4, 19, 20: widths 8, 7, 9), XOR with a carry key in {0, 1, 2}
    (55, 56: widths 8, 7) and the split (4+3)x(4+3) XOR (57). -/
def RowFacts (t a b c d e : Nat) : Prop :=
  match t with
  | 4 => a < 256 ∧ b < 256 ∧ c = a ^^^ b ∧ d = 0 ∧ e = 0
  | 19 => a < 128 ∧ b < 128 ∧ c = a ^^^ b ∧ d = 0 ∧ e = 0
  | 20 => a < 512 ∧ b < 512 ∧ c = a ^^^ b ∧ d = 0 ∧ e = 0
  | 55 => a < 256 ∧ b < 256 ∧ c < 3 ∧ d = a ^^^ b ∧ e = 0
  | 56 => a < 128 ∧ b < 128 ∧ c < 3 ∧ d = a ^^^ b ∧ e = 0
  | 57 => a < 16 ∧ b < 8 ∧ c < 16 ∧ d < 8 ∧ e = (a ^^^ c) ||| ((b ^^^ d) <<< 4)
  | _ => False

/-- The six table tags. -/
def tags : List Nat := [4, 19, 20, 55, 56, 57]

private theorem xor_lt {a b : Nat} (k : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) (hk : k ≤ 9) :
    a ^^^ b < 512 :=
  lt_of_lt_of_le (Nat.xor_lt_two_pow ha hb) (by
    calc 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 512 := by norm_num)

private theorem split_lt {a b c d : Nat} (ha : a < 16) (hb : b < 8) (hc : c < 16) (hd : d < 8) :
    ((a ^^^ c) ||| ((b ^^^ d) <<< 4)) < 512 := by
  have lo : a ^^^ c < 2 ^ 4 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hi : b ^^^ d < 2 ^ 3 := Nat.xor_lt_two_pow (by omega) (by omega)
  have shifted : (b ^^^ d) <<< 4 < 2 ^ 9 := by rw [Nat.shiftLeft_eq]; omega
  have := Nat.or_lt_two_pow (show a ^^^ c < 2 ^ 9 by omega) shifted
  omega

macro "spec_bound" : tactic => `(tactic| (
  split_ifs
  all_goals first
    | omega
    | (refine xor_lt 8 ?_ ?_ (by norm_num) <;> norm_num <;> omega)
    | (refine xor_lt 7 ?_ ?_ (by norm_num) <;> norm_num <;> omega)
    | (refine xor_lt 9 ?_ ?_ (by norm_num) <;> norm_num <;> omega)
    | (refine split_lt ?_ ?_ ?_ ?_ <;> omega)))

theorem formula_bound (n : Nat) (c : Fin 6) : (formulaRow n)[c] < 512 := by
  have b0 : spec0 n < 512 := by unfold spec0; spec_bound
  have b1 : spec1 n < 512 := by unfold spec1; spec_bound
  have b2 : spec2 n < 512 := by unfold spec2; spec_bound
  have b3 : spec3 n < 512 := by unfold spec3; spec_bound
  have b4 : spec4 n < 512 := by unfold spec4; spec_bound
  have b5 : spec5 n < 512 := by unfold spec5; spec_bound
  fin_cases c
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5

private theorem formula_facts (n : Nat) (hn : n < 606208) :
    RowFacts (spec5 n) (spec0 n) (spec1 n) (spec2 n) (spec3 n) (spec4 n) := by
  simp only [spec0, spec1, spec2, spec3, spec4, spec5]
  split_ifs <;> simp only [RowFacts] <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | trivial

private theorem cast_inj {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) {a b : Nat} (ha : a < 512)
    (hb : b < 512) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this

/-- A table row is a formula row of the native regions or of the zero padding. -/
theorem table_row {p : Nat} [Fact p.Prime] {x : Vector (ZMod p) 6}
    (h : ∃ i : Fin blake2RoundSetup.traceLen,
      x = (setupRow i.val).map (fun (v : Int) => (v : ZMod p))) :
    ∃ n < 1048576, x = (formulaRow n).map (fun (v : Nat) => (v : ZMod p)) := by
  obtain ⟨⟨i, hi⟩, row⟩ := h
  rw [traceLen_eq] at hi
  refine ⟨i, hi, ?_⟩
  rw [row, setupRow_eq i hi, Vector.map_map]
  congr 1
  funext v
  simp

/-- Membership with one of the six tags gives that region's row meaning. Padding
    rows (tag 0) never match. -/
theorem row_facts {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) {x : Vector (ZMod p) 6}
    (h : ∃ i : Fin blake2RoundSetup.traceLen,
      x = (setupRow i.val).map (fun (v : Int) => (v : ZMod p)))
    {t : Nat} (ht : t ∈ tags) (tag : x[5] = (t : ZMod p)) :
    RowFacts t x[0].val x[1].val x[2].val x[3].val x[4].val := by
  obtain ⟨n, hn, row⟩ := table_row h
  subst row
  have val (c : Nat) (hc : c < 6) : ((formulaRow n).map (fun (v : Nat) => (v : ZMod p)))[c].val =
      (formulaRow n)[c] := by
    have := formula_bound n ⟨c, hc⟩
    simp only [Fin.getElem_fin] at this
    rw [Vector.getElem_map, ZMod.val_natCast_of_lt (by omega)]
  have t512 : t < 512 := by simp only [tags, List.mem_cons, List.not_mem_nil, or_false] at ht; omega
  have tagEq : spec5 n = t := by
    rw [Vector.getElem_map] at tag
    exact cast_inj hp (by have := formula_bound n 5; simpa [formulaRow] using this) t512 tag
  have native : n < 606208 := by
    by_contra big
    have : spec5 n = 0 := by simp only [spec5]; split_ifs <;> omega
    simp only [tags, List.mem_cons, List.not_mem_nil, or_false] at ht
    omega
  have facts := formula_facts n native
  rw [tagEq] at facts
  rw [val 0 (by decide), val 1 (by decide), val 2 (by decide), val 3 (by decide),
    val 4 (by decide)]
  exact facts

/-- Typed lookup form. -/
theorem lookup_facts {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {entry : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env) {t : Nat} (ht : t ∈ tags)
    (tag : entry[5].eval env = (t : ZMod p)) :
    RowFacts t (entry[0].eval env).val (entry[1].eval env).val (entry[2].eval env).val
      (entry[3].eval env).val (entry[4].eval env).val := by
  change ∃ i : Fin blake2RoundSetup.traceLen, entry.map (Expression.eval env) =
    (setupRow i.val).map (fun (v : Int) => (v : ZMod p)) at h
  have := row_facts hp h ht (by simpa using tag)
  simpa using this

theorem entry_get {p : Nat} [Fact p.Prime] (entry : Vector (Expression (ZMod p)) 6) (j : Nat) (hj : j < 6) :
    entry.toArray[j]! = entry[j] := by
  rw [getElem!_pos entry.toArray j (by
    rw [entry.size_toArray]
    change j < size (fields 6)
    rw [show size (fields 6) = 6 from rfl]
    exact hj)]
  rfl

/-- Native Clean lookup form, for queries read off the imported operation list. -/
theorem lookup_facts_raw {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {query : Lookup (ZMod p)} {env : Environment (ZMod p)}
    (h : query.Contains env) (table : query.table = setupTable.toRaw) {t : Nat} (ht : t ∈ tags)
    (tag : (query.entry.toArray[5]!).eval env = (t : ZMod p)) :
    RowFacts t (query.entry.toArray[0]!.eval env).val (query.entry.toArray[1]!.eval env).val
      (query.entry.toArray[2]!.eval env).val (query.entry.toArray[3]!.eval env).val
      (query.entry.toArray[4]!.eval env).val := by
  rcases query with ⟨raw, entry⟩
  cases table
  simp only [entry_get entry 0 (by decide), entry_get entry 1 (by decide),
    entry_get entry 2 (by decide), entry_get entry 3 (by decide), entry_get entry 4 (by decide)]
  exact lookup_facts hp h ht (by simpa only [entry_get entry 5 (by decide)] using tag)

/-- The 192 fixed-table queries follow the two timestamp-alignment queries. -/
theorem data_tables {p : Nat} [Fact p.Prime] :
    ∀ query ∈ (FlatOperation.lookups (importedConstraints (p := p) setupTable)).drop 2,
      query.table = setupTable.toRaw := by
  dsimp only [importedConstraints, FlatOperation.lookups, List.drop]
  simp only [List.forall_mem_cons, true_and]
  exact List.forall_mem_nil _

/-- Every imported fixed-table query with one of the six tags has that region's row meaning. -/
theorem data_lookups {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ query ∈ (FlatOperation.lookups (importedConstraints setupTable)).drop 2,
      ∀ t ∈ tags, (query.entry.toArray[5]!).eval (Verification.environment w) = (t : ZMod p) →
        RowFacts t (query.entry.toArray[0]!.eval (Verification.environment w)).val
          (query.entry.toArray[1]!.eval (Verification.environment w)).val
          (query.entry.toArray[2]!.eval (Verification.environment w)).val
          (query.entry.toArray[3]!.eval (Verification.environment w)).val
          (query.entry.toArray[4]!.eval (Verification.environment w)).val := by
  intro query present t ht tag
  have member := (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).2 query
    (List.mem_of_mem_drop present)
  exact lookup_facts_raw hp member (data_tables query present) ht tag

end Airbender.Blake2Round.Proofs
