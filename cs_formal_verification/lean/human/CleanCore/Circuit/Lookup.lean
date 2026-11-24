module
public import CleanCore.Circuit.Expression
public import CleanCore.Circuit.Provable

/-! # Lookup tables (Clean `Clean.Circuit.Lookup`, pinned b41c196)

A table states what it means to contain a row (`Contains`), with two equivalent-or-weaker views for
proofs (`Soundness`, `Completeness`). A lookup asks that the evaluated entry is in the table, where the
table's contents come from the environment's prover data. Same definitions as Clean; static tables
(`StaticTable`) ignore the prover data. Deviation: Clean's witness-generation helpers (`dataGet`,
`hintGet`) are omitted. -/

@[expose] public section

namespace Airbender

variable {F : Type} {Row : TypeMap} [ProvableType Row]

structure Table (F : Type) (Row : TypeMap) [ProvableType Row] where
  name : String
  Contains : (table : Array (Row F)) → (row : Row F) → Prop
  Soundness : (table : Array (Row F)) → (row : Row F) → Prop := Contains
  Completeness : (table : Array (Row F)) → (row : Row F) → Prop := Contains
  imply_soundness : ∀ table row, Contains table row → Soundness table row
    := by intros; assumption
  implied_by_completeness : ∀ table row, Completeness table row → Contains table row
    := by intros; assumption

/-- A table with plain vector rows, as the lookups see it. -/
structure RawTable (F : Type) where
  name : String
  arity : ℕ
  Contains : Array (Vector F arity) → Vector F arity → Prop
  Soundness : Array (Vector F arity) → Vector F arity → Prop
  Completeness : Array (Vector F arity) → Vector F arity → Prop
  imply_soundness : ∀ table row, Contains table row → Soundness table row
  implied_by_completeness : ∀ table row, Completeness table row → Contains table row

structure Lookup (F : Type) where
  table : RawTable F
  entry : Vector (Expression F) table.arity

def Table.toRaw (table : Table F Row) : RawTable F where
  name := table.name
  arity := size Row
  Contains t row := table.Contains (t.map fromElements) (fromElements row)
  Soundness t row := table.Soundness (t.map fromElements) (fromElements row)
  Completeness t row := table.Completeness (t.map fromElements) (fromElements row)
  imply_soundness _ row := table.imply_soundness _ (fromElements row)
  implied_by_completeness _ row := table.implied_by_completeness _ (fromElements row)

namespace Lookup
variable [Field F]

def Contains (lookup : Lookup F) (env : Environment F) : Prop :=
  lookup.table.Contains (env.data lookup.table.name lookup.table.arity) (lookup.entry.map env)

end Lookup

structure StaticTable (F : Type) (Row : TypeMap) [ProvableType Row] where
  name : String
  length : ℕ
  row : Fin length → Row F
  index : Row F → ℕ
  Spec : Row F → Prop
  contains_iff : ∀ t, (∃ i, t = row i) ↔ Spec t

namespace StaticTable

def toTable (table : StaticTable F Row) : Table F Row where
  name := table.name
  Contains _ row := ∃ i, row = table.row i
  Soundness _ := table.Spec
  Completeness _ := table.Spec
  imply_soundness _ row := (table.contains_iff row).mp
  implied_by_completeness _ row := (table.contains_iff row).mpr

end StaticTable

def Table.fromStatic (table : StaticTable F Row) : Table F Row :=
  StaticTable.toTable table

end Airbender
