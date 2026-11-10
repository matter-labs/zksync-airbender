module
public import CleanCore.Circuit.Operations
public import Human.Helpers.Properties
public import Human.Helpers.Context.Timestamps
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-!
Concrete witness tests by evaluation. `checkOps w ops tables` evaluates every assertion of `ops` under the
assignment `w` and tests the evaluated row of the `k`-th lookup with the `k`-th checked table;
`holds_of_checkOps` turns a `true` result into `ConstraintsHoldFlat`, given that the `k`-th lookup queries the
`k`-th table (one `rfl` per circuit family). A test closes the check with one kernel evaluation (`kernel_rfl`)
instead of unfolding every constraint with `simp` and closing each resulting goal on its own. lean-strategies §2.4
prefers a once-per-family proof that the honest assignment satisfies the circuit; this single measured kernel
evaluation is the P3.3 budget brief's fallback for concrete rows (option 3): a 135-constraint, 95-lookup bigint
row costs about 0.5 s of kernel time.
-/

namespace Airbender.Verification

/-- A lookup table with a sound Boolean membership test on evaluated rows (as lists). -/
structure CheckedTable (F : Type) where
  table : RawTable F
  check : List F → Bool
  sound : ∀ row : Vector F table.arity, check row.toList = true → table.Contains #[] row

section Equality
variable {F : Type} [DecidableEq F]

/-- Is `xs = ys`, element by element (avoids the `Vector`/`Array` decidable-equality instances, whose bodies
    modules do not see). -/
def listEq : List F → List F → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && listEq xs ys
  | _, _ => false

theorem eq_of_listEq : ∀ {xs ys : List F}, listEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [listEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, eq_of_listEq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp only [listEq, Bool.false_eq_true] at h

end Equality

variable {F : Type} [Field F] [DecidableEq F]

/-- Every assertion of `ops` evaluates to zero under `w`, and the evaluated row of the `k`-th lookup passes
    the `k`-th table's test. -/
def checkOps (w : Nat → F) : List (FlatOperation F) → List (CheckedTable F) → Bool
  | [], _ => true
  | .assert e :: ops, tables => decide (e.eval (environment w) = 0) && checkOps w ops tables
  | .lookup _ :: _, [] => false
  | .lookup l :: ops, t :: tables =>
    t.check (l.entry.toList.map (Expression.eval (environment w))) && checkOps w ops tables

theorem holds_of_checkOps {w : Nat → F} {ops : List (FlatOperation F)} {tables : List (CheckedTable F)}
    (queried : (FlatOperation.lookups ops).map Lookup.table = tables.map CheckedTable.table)
    (check : checkOps w ops tables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) ops := by
  induction ops generalizing tables with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | assert e =>
      simp only [checkOps, Bool.and_eq_true, decide_eq_true_eq] at check
      exact ⟨check.1, ih queried check.2⟩
    | lookup l =>
      cases tables with
      | nil => simp only [checkOps, Bool.false_eq_true] at check
      | cons t tables =>
        simp only [FlatOperation.lookups, List.map_cons, List.cons.injEq] at queried
        simp only [checkOps, Bool.and_eq_true] at check
        refine ⟨?_, ih queried.2 check.2⟩
        obtain ⟨table, entry⟩ := l
        obtain ⟨table', test, sound⟩ := t
        obtain rfl : table = table' := queried.1
        apply sound
        rw [Vector.toList_map]
        exact check.1

/-- A table checked against rows known to be members. -/
def rowsChecked (table : RawTable F) (rows : List (Vector F table.arity))
    (members : ∀ row ∈ rows, table.Contains #[] row) : CheckedTable F where
  table := table
  check xs := rows.any fun row => listEq row.toList xs
  sound row h := by
    obtain ⟨r, mem, eq⟩ := List.any_eq_true.mp h
    obtain rfl : r = row := Vector.toList_inj.mp (eq_of_listEq eq)
    exact members r mem

/-- A static table (`T = Table.fromStatic S`, `S` found by unfolding `T`), checked by its `index`: the row at the
    computed index must equal the queried row. `rows` lists row `i` (by default `(S.row i).toList`; tables whose
    rows are `Vector.map`s pass the list form, whose map the kernel evaluates without `Array.mapM`). -/
def staticChecked {n : Nat} (T : Table F (fields n)) {S : StaticTable F (fields n)}
    (h : T = Table.fromStatic S) (rows : Fin S.length → List F := fun i => (S.row i).toList)
    (rows_eq : ∀ i, (S.row i).toList = rows i := by intro i; rfl) : CheckedTable F where
  table := T.toRaw
  check xs := if hn : xs.length = n then
      if hi : S.index ⟨⟨xs⟩, hn⟩ < S.length then listEq (rows ⟨_, hi⟩) xs else false
    else false
  sound row hc := by
    subst h
    split at hc
    · split at hc
      · rename_i hi
        exact ⟨⟨_, hi⟩, (Vector.toList_inj.mp ((rows_eq _).trans (eq_of_listEq hc))).symm⟩
      · simp only [Bool.false_eq_true] at hc
    · simp only [Bool.false_eq_true] at hc

end Airbender.Verification

namespace Airbender.Verification
variable {p : Nat} [Fact p.Prime]

/-- A native range table, checked by its bound. -/
def rangeChecked (name : String) (bound : Nat) : CheckedTable (ZMod p) where
  table := (rangeTable name bound).toRaw
  check
    | [x] => decide (x.val < bound)
    | _ => false
  sound row h := by
    obtain ⟨⟨xs⟩, size⟩ := row
    have length : xs.length = 1 := size
    match xs, length with
    | [x], _ =>
      exact (rangeTable (p := p) name bound).implied_by_completeness #[] x (of_decide_eq_true (p := x.val < bound) h)
    | [], length => simp at length
    | _ :: _ :: _, length => simp at length

/-- `range16Table`, checked. -/
def range16Checked : CheckedTable (ZMod p) := rangeChecked "Airbender.Range16" Arithmetic.limbBase

/-- `Trace.timestampTable`, checked. -/
def timestampChecked : CheckedTable (ZMod p) := rangeChecked "Airbender.Timestamp19" Trace.timestampBase

end Airbender.Verification
