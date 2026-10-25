import GKRProtocol.CleanRange

namespace Airbender.Compiler
set_option warningAsError true

theorem clean_vector_lookup (table : Table Source.BaseField (fields width))
    (expressions : Vector (_root_.Expression Source.BaseField) width)
    (environment : Environment Source.BaseField)
    (member : table.Contains (environment.data.getTable table)
      (expressions.map (fun expression => expression.eval environment))) :
    (Lookup.mk table.toRaw expressions).Contains environment := by
  exact member

theorem clean_scalar_lookup (table : Table Source.BaseField field)
    (expression : _root_.Expression Source.BaseField) (environment : Environment Source.BaseField)
    (member : table.Contains (environment.data.getTable table) (expression.eval environment)) :
    (Lookup.mk table.toRaw #v[expression]).Contains environment := by
  convert member using 1
  simp only [Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem clean_range16_lookup (expression : _root_.Expression Source.BaseField)
    (environment : Environment Source.BaseField) (bounded : (expression.eval environment).val < 65536) :
    (Verification.range16 expression).Contains environment := by
  have member := range16_clean_contains (expression.eval environment) bounded
    (environment.data.getTable (Verification.range16Table (p := babyBearModulus)))
  convert member using 1
  simp only [Verification.range16, Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem clean_timestamp_lookup (expression : _root_.Expression Source.BaseField)
    (environment : Environment Source.BaseField) (bounded : (expression.eval environment).val < 524288) :
    (Trace.timestampLookup expression).Contains environment := by
  have member := timestamp_clean_contains (expression.eval environment) bounded
    (environment.data.getTable (Trace.timestampTable (p := babyBearModulus)))
  convert member using 1
  simp only [Trace.timestampLookup, Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

end Airbender.Compiler
