import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

theorem clean_pair_lookup (table : Table Source.BaseField fieldPair)
    (key value : _root_.Expression Source.BaseField) (environment : Environment Source.BaseField)
    (member : table.Contains (environment.data.getTable table)
      (key.eval environment, value.eval environment)) :
    (Verification.pairLookup table key value).Contains environment := by
  convert member using 1
  simp only [Verification.pairLookup, Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem clean_triple_lookup (table : Table Source.BaseField fieldTriple)
    (first second third : _root_.Expression Source.BaseField) (environment : Environment Source.BaseField)
    (member : table.Contains (environment.data.getTable table)
      (first.eval environment, second.eval environment, third.eval environment)) :
    (Lookup.mk table.toRaw #v[first, second, third]).Contains environment := by
  convert member using 1
  simp only [Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

end Airbender.Compiler
