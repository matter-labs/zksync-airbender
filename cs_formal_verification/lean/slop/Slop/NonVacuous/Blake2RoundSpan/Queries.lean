module
public import Slop.NonVacuous.Blake2RoundSpan.Tables
public import Slop.Blake2Round.GRows

@[expose] public section

/-! A fixed-table query of the round circuit, given as its imported entry (`importedConstraints.lookup_i`), holds
    when its entries evaluate to values with the row meaning of its tag (the converse of
    `Blake2Round.Proofs.query_4` … `query_57`). The per-call modules prove only the entry evaluations. The
    imported lookup list is named `L` (`hL`) so that no caller elaborates a goal over the literal list (each such
    goal unfolds it). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} {L : List (Lookup (ZMod p))}
  (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
  {hn : n < L.length} {i : Nat}
  {hi : i < (FlatOperation.lookups (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable)).length}
  {entry : Vector (Expression (ZMod p)) 6}
  (hq : (FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable)).get ⟨i, hi⟩ =
    Lookup.mk Blake2Round.setupTable.toRaw entry) (index : n = i)
include hL hq index

/-- A plain XOR query (tag 4, 19 or 20 for widths 8, 7, 9). -/
theorem contains_xor {width t : Nat} (kind : (width = 8 ∧ t = 4) ∨ (width = 7 ∧ t = 19) ∨ (width = 9 ∧ t = 20))
    {a b c : ZMod p} (facts : ChunkXor width a.val b.val c.val)
    (tag : entry[5].eval (Verification.environment w) = (t : ZMod p))
    (ha : entry[0].eval (Verification.environment w) = a) (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c) (hd : entry[3].eval (Verification.environment w) = 0)
    (he : entry[4].eval (Verification.environment w) = 0) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hL index
  rw [hq]
  obtain ⟨x, y, z⟩ := facts
  refine setup_contains (t := t) ?_ ha hb hc hd he tag
  rw [ZMod.val_zero]
  rcases kind with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨x, y, z, rfl, rfl⟩
  · exact ⟨x, y, z, rfl, rfl⟩
  · exact ⟨x, y, z, rfl, rfl⟩

/-- An XOR-with-carry query (tag 55 or 56 for widths 8 and 7). -/
theorem contains_carry {width t : Nat} (kind : (width = 8 ∧ t = 55) ∨ (width = 7 ∧ t = 56))
    {a b c d : ZMod p} (facts : ChunkXor width a.val b.val d.val) (carry : c.val < 3)
    (tag : entry[5].eval (Verification.environment w) = (t : ZMod p))
    (ha : entry[0].eval (Verification.environment w) = a) (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c) (hd : entry[3].eval (Verification.environment w) = d)
    (he : entry[4].eval (Verification.environment w) = 0) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hL index
  rw [hq]
  obtain ⟨x, y, z⟩ := facts
  refine setup_contains (t := t) ?_ ha hb hc hd he tag
  rw [ZMod.val_zero]
  rcases kind with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨x, y, carry, z, rfl⟩
  · exact ⟨x, y, carry, z, rfl⟩

/-- The split (4+3)×(4+3) XOR query (tag 57). -/
theorem contains_split {a b c d e : ZMod p} (facts : SplitXor a.val b.val c.val d.val e.val)
    (tag : entry[5].eval (Verification.environment w) = ((57 : Nat) : ZMod p))
    (ha : entry[0].eval (Verification.environment w) = a) (hb : entry[1].eval (Verification.environment w) = b)
    (hc : entry[2].eval (Verification.environment w) = c) (hd : entry[3].eval (Verification.environment w) = d)
    (he : entry[4].eval (Verification.environment w) = e) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hL index
  rw [hq]
  exact setup_contains (t := 57) facts ha hb hc hd he tag

end Airbender.NonVacuous.Blake2RoundSpan
