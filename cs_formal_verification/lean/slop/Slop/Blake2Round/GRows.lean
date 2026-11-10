module
public import Slop.Blake2Round.GTrace
public import Slop.Blake2Round.Lookups
public import Slop.Blake2Round.OpIndex
public import Slop.Eval
public import Slop.Templates
public import Mathlib.Tactic.ReduceModChar
public import Slop.Blake2Round.ArtifactChecks

@[expose] public section

set_option warningAsError true

/-!
From one fixed-table query of the round circuit to the chunk fact of `GTrace` fields.
Each lemma takes the query as its imported entry and the equalities between the
evaluated entry columns and the trace fields; the per-call modules prove only those
equalities, by evaluation and field arithmetic.
-/

namespace Airbender.Blake2Round.Proofs

/-- Equality of linear forms over BabyBear, with coefficients reduced modulo the prime. -/
macro "mod_ring" : tactic => `(tactic| (rw [← sub_eq_zero]; ring_nf; try reduce_mod_char))

variable {p : Nat}

/-- Lookup `i` of the round circuit is in range (194 lookups). -/
theorem query_lt [Fact p.Prime] {i : Nat} (hi : i < 194) :
    i < (FlatOperation.lookups (importedConstraints (p := p) setupTable)).length := by
  rw [lookup_count]; exact hi

/-- Constraint `i` of the round circuit is in range (220 constraints). -/
theorem constraint_lt [Fact p.Prime] {i : Nat} (hi : i < 220) :
    i < (FlatOperation.constraints (importedConstraints (p := p) setupTable)).length := by
  rw [constraint_count]; exact hi

section Queries

variable [Fact p.Prime] (hp : 512 ≤ p) {w : Nat → ZMod p}
  (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setupTable))
  {i : Nat} {hi : i < (FlatOperation.lookups (importedConstraints setupTable)).length}
  {entry : Vector (Expression (ZMod p)) 6}
  (hq : (FlatOperation.lookups (importedConstraints setupTable)).get ⟨i, hi⟩ =
    Lookup.mk setupTable.toRaw entry)

include hp h hq

/-- One fixed-table query of the round circuit, given as its imported entry
    (`importedConstraints.lookup_i`), has the row meaning of its tag. The per-tag
    lemmas below turn it into the chunk fact of the trace fields that the entry
    columns evaluate to; each call proves only those evaluations. -/
theorem query_row {t : Nat} (ht : t ∈ tags)
    (tag : entry[5].eval (Verification.environment w) = t) :
    RowFacts t (entry[0].eval (Verification.environment w)).val
      (entry[1].eval (Verification.environment w)).val
      (entry[2].eval (Verification.environment w)).val
      (entry[3].eval (Verification.environment w)).val
      (entry[4].eval (Verification.environment w)).val := by
  have member := Verification.lookup_of_holds h ⟨i, hi⟩
  rw [hq] at member
  exact lookup_facts hp member ht tag

theorem query_4 (tag : entry[5].eval (Verification.environment w) = 4) {a b c : ZMod p}
    (ha : entry[0].eval (Verification.environment w) = a)
    (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c) : ChunkXor 8 a.val b.val c.val := by
  have row := query_row hp h hq (t := 4) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst ha hb hc
  exact ⟨row.1, row.2.1, row.2.2.1⟩

theorem query_19 (tag : entry[5].eval (Verification.environment w) = 19) {a b c : ZMod p}
    (ha : entry[0].eval (Verification.environment w) = a)
    (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c) : ChunkXor 7 a.val b.val c.val := by
  have row := query_row hp h hq (t := 19) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst ha hb hc
  exact ⟨row.1, row.2.1, row.2.2.1⟩

theorem query_20 (tag : entry[5].eval (Verification.environment w) = 20) {a b c : ZMod p}
    (ha : entry[0].eval (Verification.environment w) = a)
    (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c) : ChunkXor 9 a.val b.val c.val := by
  have row := query_row hp h hq (t := 20) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst ha hb hc
  exact ⟨row.1, row.2.1, row.2.2.1⟩

theorem query_55 (tag : entry[5].eval (Verification.environment w) = 55) {a b d : ZMod p}
    (ha : entry[0].eval (Verification.environment w) = a)
    (hb : entry[1].eval (Verification.environment w) = b)
    (hd : entry[3].eval (Verification.environment w) = d) : ChunkXor 8 a.val b.val d.val := by
  have row := query_row hp h hq (t := 55) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst ha hb hd
  exact ⟨row.1, row.2.1, row.2.2.2.1⟩

theorem carry_55 (tag : entry[5].eval (Verification.environment w) = 55) {c : ZMod p}
    (hc : entry[2].eval (Verification.environment w) = c) : c.val < 3 := by
  have row := query_row hp h hq (t := 55) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst hc
  exact row.2.2.1

theorem query_56 (tag : entry[5].eval (Verification.environment w) = 56) {a b d : ZMod p}
    (ha : entry[0].eval (Verification.environment w) = a)
    (hb : entry[1].eval (Verification.environment w) = b)
    (hd : entry[3].eval (Verification.environment w) = d) : ChunkXor 7 a.val b.val d.val := by
  have row := query_row hp h hq (t := 56) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst ha hb hd
  exact ⟨row.1, row.2.1, row.2.2.2.1⟩

theorem carry_56 (tag : entry[5].eval (Verification.environment w) = 56) {c : ZMod p}
    (hc : entry[2].eval (Verification.environment w) = c) : c.val < 3 := by
  have row := query_row hp h hq (t := 56) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst hc
  exact row.2.2.1

theorem query_57 (tag : entry[5].eval (Verification.environment w) = 57) {a b c d e : ZMod p}
    (ha : entry[0].eval (Verification.environment w) = a)
    (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c)
    (hd : entry[3].eval (Verification.environment w) = d)
    (he : entry[4].eval (Verification.environment w) = e) :
    SplitXor a.val b.val c.val d.val e.val := by
  have row := query_row hp h hq (t := 57) (by decide) (by rw [tag, Nat.cast_ofNat])
  subst ha hb hc hd he
  exact row

end Queries

/-- A Boolean column, given as its imported constraint `x * (x - 1)`
    (`importedConstraints.constraint_i`), is a carry below 3. -/
theorem flag_carry [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    {i : Nat} {hi : i < (FlatOperation.constraints (importedConstraints setupTable)).length}
    {e : Expression (ZMod p)} (hc : (FlatOperation.constraints (importedConstraints setupTable)).get
      ⟨i, hi⟩ = e) {x : ZMod p} (hx : e.eval (Verification.environment w) = x * (x + -1)) :
    x.val < 3 := by
  have := Arithmetic.boolean_val (Templates.bit_of_eval h hc hx)
  omega

end Airbender.Blake2Round.Proofs
