module
public import Human.Import.Proth120
public meta import Human.Import.Proth120
public import Human.Import.TranscribeCommand
public meta import Human.Import.TranscribeCommand
public import Human.Import.InitsTeardownsLayout
public meta import Human.Import.InitsTeardownsLayout
public import Human.Import.Operations
public meta import Human.Import.Operations
public meta import Human.Import.Exec.FastColumns

public meta section
namespace Airbender.UnifiedReduced.Proth120
open Lean Elab Command

private instance {n : Nat} : ToExpr (Vector Nat n) where
  toExpr a := mkApp4 (mkConst ``Vector.mk [0]) (mkConst ``Nat) (mkNatLit n) (toExpr a.toArray)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit n))
  toTypeExpr := mkApp2 (mkConst ``Vector [0]) (mkConst ``Nat) (mkNatLit n)

deriving instance ToExpr for Airbender.Json.Value
deriving instance ToExpr for RowSource
deriving instance ToExpr for Airbender.Trace.TimestampPort
deriving instance ToExpr for Airbender.Trace.TraceColumns
deriving instance ToExpr for Airbender.Trace.DecoderColumns
deriving instance ToExpr for Airbender.Verification.IndirectPort
deriving instance ToExpr for Airbender.Trace.MemoryAddress
deriving instance ToExpr for Airbender.Trace.WordColumns
deriving instance ToExpr for Airbender.Trace.MemoryPort

private abbrev J := Airbender.Json.Value
private abbrev E := Airbender.Expression Int

/-- Retain the native RAM cache and product graph along with the shared layout metadata.
    Timestamp ports use the number of timestamp queries. Their actual expressions are read below. -/
private def metadata (obj : J) : Except String Circuit := do
  let layers ← (← jsonArray (← jsonMember obj "layers")).mapM fun layer => do
    let gates (key : String) := do
      let mut selected := #[]
      for g in ← jsonArray (← jsonMember layer key) do
        let .obj [(tag, _)] ← jsonMember g "enforced_relation" | throw "malformed native gate"
        if ["InitsOrTeardownsInitialPair", "InitialGrandProductFromCaches", "TrivialProduct",
            "MaskIntoIdentityProduct", "CopyInBaseField", "CopyInExtensionField"].contains tag then
          selected := selected.push (← Decode.decode g)
      return selected
    let caches ← (← jsonArray (← jsonMember layer "cached_relations")).filterMapM fun v => do
      let .arr [_, .obj [(tag, _)]] := v | throw "invalid cached relation"
      if tag == "MemoryTuple" then some <$> Decode.decode v else pure none
    return (⟨← fieldAs layer "layer", ← gates "gates_with_external_connections", caches.toArray, ← gates "gates",
      ← fieldAs layer "intermediate_layer_width"⟩ : GKRLayerDescription)
  let clocks ← jsonArray (← jsonMember obj "timestamp_range_check_lookup_expressions")
  let zero : Coefficient := ⟨⟨0, by decide⟩⟩
  return { trace_len := ← fieldAs obj "trace_len", memory_layout := ← fieldAs obj "memory_layout",
           witness_layout := ← fieldAs obj "witness_layout", layers := layers.toArray,
           placement_data := ← fieldAs obj "placement_data", aux_layout_data := ← fieldAs obj "aux_layout_data",
           scratch_space_mapping := ← fieldAs obj "scratch_space_mapping",
           scratch_space_mapping_rev := ← fieldAs obj "scratch_space_mapping_rev",
           timestamp_range_check_lookup_expressions := clocks.toArray.mapIdx fun i _ => ⟨⟨#[], zero⟩, i⟩,
           table_offsets := ← fieldAs obj "table_offsets", total_tables_size := ← fieldAs obj "total_tables_size",
           offset_for_decoder_table := ← fieldAs obj "offset_for_decoder_table",
           has_decoder_lookup := ← fieldAs obj "has_decoder_lookup",
           num_generic_lookups := ← fieldAs obj "num_generic_lookups",
           generic_lookup_tables_width := ← fieldAs obj "generic_lookup_tables_width",
           tables_ids_in_generic_lookups := ← fieldAs obj "tables_ids_in_generic_lookups",
           global_output_map := ← fieldAs obj "global_output_map", scratch_space_size := 0, decode_table_columns_mask := #[],
           degree_1_constraints := #[], degree_2_constraints := #[], structured_statements := #[],
           range_check_16_lookup_expressions := #[], generic_lookups := #[], variable_names := ⟨#[]⟩, _marker := .null }

private def term : E → CommandElabM (TSyntax `term)
  | .const n => do
    let lit ← if n ≥ 0 then `(Int.ofNat $(quote n.toNat)) else `(Int.negSucc $(quote (-n - 1).toNat))
    `(Airbender.Expression.const (Int.cast $lit))
  | .var v => `(Airbender.Expression.var ⟨$(quote v.index)⟩)
  | .add a b => do `(Airbender.Expression.add $(← term a) $(← term b))
  | .mul a b => do `(Airbender.Expression.mul $(← term a) $(← term b))

private def readOrFail (x : Except String α) : CommandElabM α :=
  match x with | .ok a => pure a | .error msg => throwError "Proth120 layout: {msg}"

/-- Transcribe the retained equations, range queries, pooled lookup entries and inline window geometry. -/
elab "import_proth120_rows " name:ident layoutName:ident " from " path:str : command => do
  let bytes := (← IO.FS.readFile path.getString).toUTF8
  let json ← readOrFail <| Json.parse bytes
  let c ← readOrFail <| metadata json
  let pl := c.placements
  let source ← readOrFail (RowSource.read json)
  let ss ← readOrFail (source.statements.mapM statement)
  let ranges ← readOrFail (RowSource.scalars source.ranges c)
  let queries ← readOrFail (source.tables c)
  let timestamps ← readOrFail (RowSource.scalars source.clocks c)
  let eqs ← ss.mapM fun e => do `(Airbender.FlatOperation.assert $(← term e))
  let small ← ranges.mapM fun e => do `(Airbender.FlatOperation.lookup (Airbender.Verification.range16 $(← term e)))
  let setup := mkIdent `setup
  let tables ← queries.mapM fun q => do
    let entries ← q.toArray.mapM term
    `(Airbender.FlatOperation.lookup { table := ($setup).toRaw, entry := #v[$[$entries],*] })
  let ops := (eqs ++ small ++ tables).toArray
  let prime := mkIdent `p
  elabCommand (← `(def $name {$prime : Nat} [Fact (Nat.Prime $prime)] ($setup : Airbender.Table (ZMod $prime) (Airbender.fields 10)) :
    List (Airbender.FlatOperation (ZMod $prime)) := [$[$ops],*]))
  let clockOps := (← timestamps.mapM fun e => do
    `(Airbender.FlatOperation.lookup (Airbender.Trace.timestampLookup $(← term e)))).toArray
  let clockName := mkIdent (name.getId.appendAfter "TimestampLookups")
  elabCommand (← `(def $clockName {$prime : Nat} [Fact (Nat.Prime $prime)] : List (Airbender.FlatOperation (ZMod $prime)) :=
    [$[$clockOps],*]))
  let base := (← getCurrNamespace) ++ name.getId
  let columns ← readOrFail (Fast.traceColumns pl c)
  let ports ← readOrFail (Fast.memoryPorts pl c)
  let decoder ← readOrFail (Fast.decoderColumns pl c)
  liftCoreM do
    addTranscribedDef (base.appendAfter "Source") (toTypeExpr RowSource) (toExpr source)
    addTranscribedDef (base.appendAfter "LayoutSource") (toTypeExpr Circuit) (toExpr c)
    addTranscribedDef (base.appendAfter "TraceColumns") (toTypeExpr Trace.TraceColumns) (toExpr columns)
    addTranscribedDef (base.appendAfter "MemoryPorts") (toTypeExpr (Array Trace.MemoryPort)) (toExpr ports)
    addTranscribedDef (base.appendAfter "DecoderColumns") (toTypeExpr Trace.DecoderColumns) (toExpr decoder)
  let layout ← readOrFail (c.initsTeardownsLayout false)
  let pair (v : Vector Nat 2) := `(#v[$(quote v[0]), $(quote v[1])])
  let sets := (← layout.sets.mapM fun s => do
    `(Airbender.InitsTeardowns.TeardownSet.mk $(← pair s.value) $(← pair s.timestamp)))
  elabCommand (← `(def $layoutName : Airbender.InitsTeardowns.Layout :=
    ⟨$(quote layout.traceLog), $(quote layout.wordBits), #[$[$sets],*]⟩))

end Airbender.UnifiedReduced.Proth120
