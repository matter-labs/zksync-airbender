module
public import CleanCore.Circuit.Operations
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Completeness of a query into any static table (lean-strategies §2.1): the query holds when its
evaluated entry is the row at the table's own index. A witness test then checks one closed fact per
query instead of unfolding the table or the artifact. -/

namespace Airbender.Verification

theorem static_lookup_contains {p : Nat} [Fact p.Prime] {Row : TypeMap} [ProvableType Row]
    (t : StaticTable (ZMod p) Row) (entry : Vector (Expression (ZMod p)) (size Row))
    (env : Airbender.Environment (ZMod p))
    (bound : t.index (fromElements (entry.map (Expression.eval env))) < t.length)
    (row : ∀ h : t.index (fromElements (entry.map (Expression.eval env))) < t.length,
      fromElements (entry.map (Expression.eval env)) = t.row ⟨_, h⟩) :
    (Lookup.mk (Table.fromStatic t).toRaw entry).Contains env :=
  ⟨⟨_, bound⟩, row bound⟩

end Airbender.Verification
