module
public import CleanCore.Circuit.Lookup

/-! # Lookup soundness and completeness views and the lemmas the proofs cite (Clean `Clean.Circuit.Lookup` and
`Clean.Circuit.Provable`, pinned b41c196, transcribed with proofs). -/

@[expose] public section

namespace Airbender

variable {F : Type}

/-- Evaluate every entry of a row of expressions (Clean's `ProvableType.eval`). -/
def ProvableType.eval {F : Type} [Field F] {M : TypeMap} [ProvableType M] (env : Environment F)
    (x : M (Expression F)) : M F :=
  fromElements ((toElements x).map (Expression.eval env))

def ProverData.getTable (data : ProverData F) {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) : Array (Row F) :=
  data table.name (size Row) |>.map fromElements

namespace Lookup
variable [Field F]

def Soundness (lookup : Lookup F) (env : Environment F) : Prop :=
  lookup.table.Soundness (env.data lookup.table.name lookup.table.arity) (lookup.entry.map env)

def Completeness (lookup : Lookup F) (env : Environment F) : Prop :=
  lookup.table.Completeness (env.data lookup.table.name lookup.table.arity) (lookup.entry.map env)

theorem soundess_def {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) (env : Environment F) (entry : Row (Expression F)) :
    let lookup : Lookup F := { table := table.toRaw, entry := toElements entry };
    lookup.Soundness env ↔ table.Soundness (env.data.getTable table) (ProvableType.eval env entry) :=
  Iff.rfl

theorem soundess_def_field (table : Table F field) (env : Environment F) (entry : Expression F) :
    let lookup : Lookup F := { table := table.toRaw, entry := #v[entry] };
    lookup.Soundness env ↔ table.Soundness (env.data.getTable table) (entry.eval env) := by
  simp only [Soundness, Table.toRaw, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem completeness_def {Row : TypeMap} [ProvableType Row]
    (table : Table F Row) (env : Environment F) (entry : Row (Expression F)) :
    let lookup : Lookup F := { table := table.toRaw, entry := toElements entry };
    lookup.Completeness env ↔ table.Completeness (env.data.getTable table) (ProvableType.eval env entry) :=
  Iff.rfl

theorem completeness_def_field (table : Table F field) (env : Environment F) (entry : Expression F) :
    let lookup : Lookup F := { table := table.toRaw, entry := #v[entry] };
    lookup.Completeness env ↔ table.Completeness (env.data.getTable table) (entry.eval env) := by
  simp only [Completeness, Table.toRaw, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

end Lookup

end Airbender
