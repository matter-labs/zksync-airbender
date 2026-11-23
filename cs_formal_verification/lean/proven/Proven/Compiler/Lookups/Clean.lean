module
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Context.Timestamps
public import Proven.CleanCore.Circuit.Lookup

@[expose] public section
namespace Airbender.Compiler
open NativeArithmetic
set_option warningAsError true

theorem clean_vector_lookup (table : Table F (fields width))
    (expressions : Vector (Airbender.Expression F) width) (environment : Environment F)
    (member : table.Contains (environment.data.getTable table)
      (expressions.map (fun expression => expression.eval environment))) :
    (Lookup.mk table.toRaw expressions).Contains environment := by
  exact member

theorem clean_scalar_lookup (table : Table F field)
    (expression : Airbender.Expression F) (environment : Environment F)
    (member : table.Contains (environment.data.getTable table) (expression.eval environment)) :
    (Lookup.mk table.toRaw #v[expression]).Contains environment := by
  convert member using 1
  simp only [Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

end Airbender.Compiler

namespace Airbender.Compiler
open NativeArithmetic

theorem clean_timestamp_lookup (expression : Airbender.Expression F) (environment : Environment F)
    (bounded : (expression.eval environment).val < 524288) :
    (Trace.timestampLookup expression).Contains environment := by
  apply clean_scalar_lookup
  change ∃ index : Fin 524288, expression.eval environment = (index.val : F)
  exact ⟨⟨(expression.eval environment).val, bounded⟩,
    (ZMod.natCast_zmod_val (expression.eval environment)).symm⟩

end Airbender.Compiler
