import Slop.ShiftBinop.ArtifactChecks
import Slop.ShiftBinop.OpIndex
import Slop.Eval
import Mathlib.Tactic.FinCases

/-! Completeness of the shift/binary table queries, proved once for every row (lean-strategies §2.1):
each query's entry is its row's columns, so a query holds when those columns are a table row. -/

namespace Airbender.ShiftBinop.Proofs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384

/-- Column `k` of byte query `i` (`k < 8` are the leading entries, `8` is the tag). -/
def queryColumn (i : Fin 4) (k : Nat) : Nat := 56 + 9 * i.val + k

theorem query_arity {p : Nat} [Fact p.Prime] (i : Fin 4) :
    ((FlatOperation.lookups (importedConstraints (p := p))).get
      ⟨3 + i.val, by rw [lookup_count]; omega⟩).table.arity = 10 := by
  fin_cases i <;> rfl

/-- Byte query `i`'s entry at its checked width. -/
def queryEntry {p : Nat} [Fact p.Prime] (i : Fin 4) : Vector (Expression (ZMod p)) 10 :=
  ((FlatOperation.lookups (importedConstraints (p := p))).get
    ⟨3 + i.val, by rw [lookup_count]; omega⟩).entry.cast (query_arity i)

theorem query_shape {p : Nat} [Fact p.Prime] (i : Fin 4) :
    (FlatOperation.lookups (importedConstraints (p := p))).get ⟨3 + i.val, by rw [lookup_count]; omega⟩ =
      Verification.shiftBinopLookup (queryEntry i) := by
  fin_cases i <;> rfl

/-- The values of byte query `i`'s columns, in entry order. -/
def queryValues {p : Nat} (w : Nat → ZMod p) (i : Fin 4) : Vector (ZMod p) 10 :=
  #v[w (queryColumn i 0), w (queryColumn i 1), w (queryColumn i 2), w (queryColumn i 3),
    w (queryColumn i 4), w (queryColumn i 5), w (queryColumn i 6), w (queryColumn i 7), 0,
    w (queryColumn i 8)]

/-- The values of the sign/truncation query's columns, in entry order. -/
def signValues {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 10 :=
  #v[w 52, w 53, w 54, 0, 0, 0, 0, 0, 0, w 55]

/-- The setup-table row of an entry, by its tag (the table's own index function). -/
def rowIndex {p : Nat} (xs : Vector (ZMod p) 10) : Nat :=
  match xs[9].val with
  | 3 => 1 + xs[0].val
  | 4 => 257 + xs[0].val * 256 + xs[1].val
  | 6 => 65793 + xs[0].val * 256 + xs[1].val
  | 7 => 131329 + xs[0].val * 256 + xs[1].val
  | 8 => 196865 + xs[0].val * 256 + xs[1].val
  | 9 => 262401 + xs[0].val * 65536 + xs[1].val * 256 + xs[2].val * 8 + xs[3].val
  | _ => 0

/-- The setup-table row named by an entry's tag and operands. -/
def rowAt {p : Nat} (xs : Vector (ZMod p) 10) : Fin 524545 := ⟨rowIndex xs % 524545, Nat.mod_lt _ (by decide)⟩

theorem query_values {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (i : Fin 4) :
    (queryEntry i).map (Expression.eval (Verification.environment w)) = queryValues w i := by
  rw [← Vector.toArray_inj, Vector.toArray_map, queryEntry, Vector.toArray_cast]
  fin_cases i
  all_goals simp only [queryValues, queryColumn]
  all_goals op_index
  all_goals eval_entry [Fin.val_mk, Nat.reduceMul, Vector.toArray_mk, Verification.shiftBinopLookup]

/-- Byte query `i` holds when its column values are the setup row at their index. -/
theorem query_of_columns {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} (i : Fin 4)
    (values : queryValues w i =
      (Verification.shiftBinopRow (rowAt (queryValues w i))).map (fun (n : Nat) => (n : ZMod p))) :
    ((FlatOperation.lookups (importedConstraints (p := p))).get
      ⟨3 + i.val, by rw [lookup_count]; omega⟩).Contains (Verification.environment w) := by
  rw [query_shape]
  change ∃ index : Fin 524545, (queryEntry i).map (Expression.eval (Verification.environment w)) =
    (Verification.shiftBinopRow index).map (fun (n : Nat) => (n : ZMod p))
  exact ⟨_, by rw [query_values]; exact values⟩

theorem sign_arity {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints (p := p))).get
      ⟨2, by rw [lookup_count]; decide⟩).table.arity = 10 := rfl

/-- The sign/truncation query's entry at its checked width. -/
def signEntry {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 10 :=
  ((FlatOperation.lookups (importedConstraints (p := p))).get
    ⟨2, by rw [lookup_count]; decide⟩).entry.cast sign_arity

theorem sign_shape {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).get ⟨2, by rw [lookup_count]; decide⟩ =
      Verification.shiftBinopLookup signEntry := rfl

/-- The sign/truncation query holds when its column values are the setup row at their index. -/
theorem sign_query_of_columns {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (values : signValues w =
      (Verification.shiftBinopRow (rowAt (signValues w))).map (fun (n : Nat) => (n : ZMod p))) :
    ((FlatOperation.lookups (importedConstraints (p := p))).get
      ⟨2, by rw [lookup_count]; decide⟩).Contains (Verification.environment w) := by
  rw [sign_shape]
  change ∃ index : Fin 524545, signEntry.map (Expression.eval (Verification.environment w)) =
    (Verification.shiftBinopRow index).map (fun (n : Nat) => (n : ZMod p))
  refine ⟨rowAt (signValues w), ?_⟩
  rw [← values, signValues, ← Vector.toArray_inj, Vector.toArray_map, signEntry, Vector.toArray_cast]
  op_index
  eval_entry [Vector.toArray_mk, Verification.shiftBinopLookup]

end Airbender.ShiftBinop.Proofs
