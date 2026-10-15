import Airbender.Import.Schema

namespace Airbender.Setup
open Lean

/-- Lossless blocks of actual canonical field values, not table-generation rules. -/
inductive Block where
  | affine (length first : Nat) (step : Int)
  | dense (values : Array Nat)
  | periodic (repetitions : Nat) (stride : Int) (values : Array Nat)
  deriving Repr, DecidableEq

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing setup JSON fields"

instance : FromJson Block where
  fromJson? json := do
    let kind : String ← fromJson? (← json.getObjVal? "kind")
    match kind with
    | "affine" =>
      exactKeys json #["kind", "length", "first", "step"]
      return .affine (← fromJson? (← json.getObjVal? "length"))
        (← fromJson? (← json.getObjVal? "first")) (← fromJson? (← json.getObjVal? "step"))
    | "dense" =>
      exactKeys json #["kind", "values"]
      return .dense (← fromJson? (← json.getObjVal? "values"))
    | "periodic" =>
      exactKeys json #["kind", "repetitions", "stride", "values"]
      return .periodic (← fromJson? (← json.getObjVal? "repetitions"))
        (← fromJson? (← json.getObjVal? "stride")) (← fromJson? (← json.getObjVal? "values"))
    | _ => throw "unknown setup column encoding"

def Block.length : Block → Nat
  | .affine length _ _ => length
  | .dense values => values.size
  | .periodic repetitions _ values => repetitions * values.size

def Block.get? (block : Block) (index : Nat) : Option Nat :=
  if index < block.length then
    match block with
    | .affine _ first step =>
      let value := (first : Int) + step * index
      if 0 ≤ value then some value.toNat else none
    | .dense values => values[index]?
    | .periodic _ stride values =>
      let value := ((values[index % values.size]?.getD 0 : Nat) : Int) + stride * (index / values.size)
      if 0 ≤ value then some value.toNat else none
  else none

structure Column where
  blocks : Array Block
  deriving Repr, DecidableEq, FromJson

def getFromBlocks : List Block → Nat → Option Nat
  | [], _ => none
  | block :: rest, index =>
    if index < block.length then block.get? index
    else getFromBlocks rest (index - block.length)

def Column.get? (column : Column) (index : Nat) : Option Nat :=
  getFromBlocks column.blocks.toList index

def Column.validate (column : Column) (length bound : Nat) : Except String Unit := do
  let mut covered := 0
  for block in column.blocks do
    unless 0 < block.length do throw "empty setup column block"
    covered := covered + block.length
    unless covered ≤ length do throw "setup column exceeds its domain"
    match block with
    | .affine _ first step =>
      unless first < 4294967296 && -9223372036854775808 ≤ step && step < 9223372036854775808 do
        throw "setup affine encoding exceeds Rust integer bounds"
      for index in #[0, block.length - 1] do
        let some value := block.get? index | throw "negative setup column value"
        unless value < bound do throw "noncanonical setup field element"
    | .dense values =>
      unless values.all (· < bound) do throw "noncanonical setup field element"
    | .periodic repetitions stride values =>
      unless -9223372036854775808 ≤ stride && stride < 9223372036854775808 do
        throw "setup periodic encoding exceeds Rust integer bounds"
      for first in values do
        let last := (first : Int) + stride * (repetitions - 1)
        unless first < bound && 0 ≤ last && last < bound do
          throw "noncanonical setup field element"
  unless covered == length do throw "setup column does not cover its domain"

structure Region where
  id : Nat
  offset : Nat
  length : Nat
  width : Nat
  key_columns : Nat
  deriving Repr, DecidableEq, FromJson

structure Program where
  image_words : Nat
  image : Column
  text_words : Nat
  text : Column
  deriving Repr, DecidableEq, FromJson

/-- The circuit and all materialized lookup setup columns share one artifact.
    Setup field values are canonical; circuit coefficients retain their native
    Montgomery encoding through the existing circuit schema. -/
structure Artifact where
  version : Nat
  field_modulus : Nat
  trace_len : Nat
  circuit : Circuit
  program : Option Program
  tables : Array Region
  columns : Array Column
  range16 : Column
  timestamp_range : Column
  deriving Repr, FromJson

def Artifact.validate (artifact : Artifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == babyBearModulus do
    throw "unsupported setup artifact version or field"
  unless 0 < artifact.trace_len && artifact.trace_len &&& (artifact.trace_len - 1) == 0 do
    throw "setup trace length must be a power of two"
  unless artifact.circuit.trace_len == artifact.trace_len &&
      artifact.circuit.generic_lookup_tables_width == artifact.columns.size do
    throw "setup JSON and circuit shapes differ"
  for column in artifact.columns do column.validate artifact.trace_len artifact.field_modulus
  artifact.range16.validate artifact.trace_len artifact.field_modulus
  artifact.timestamp_range.validate artifact.trace_len artifact.field_modulus
  if let some program := artifact.program then
    program.image.validate program.image_words 4294967296
    program.text.validate program.text_words 4294967296
  let mut endOffset := 0
  let mut previousId : Option Nat := none
  for table in artifact.tables do
    if let some id := previousId then
      unless id < table.id do throw "setup table IDs are not strictly increasing"
    unless table.offset == endOffset && 0 < table.length &&
        table.key_columns ≤ table.width && table.width < artifact.columns.size do
      throw "invalid setup table region"
    unless (artifact.circuit.table_offsets[table.id]?.map (·.val)) == some table.offset do
      throw "setup table offset differs from circuit"
    endOffset := endOffset + table.length
    previousId := some table.id
  unless artifact.circuit.offset_for_decoder_table == endOffset do
    throw "decoder offset differs from materialized tables"
  unless endOffset ≤ artifact.circuit.total_tables_size &&
      artifact.circuit.total_tables_size ≤ artifact.trace_len do
    throw "invalid decoder/setup extent"
  if artifact.circuit.has_decoder_lookup && artifact.program.isNone then
    throw "decoder setup export requires its selected program inputs"
  unless artifact.circuit.has_decoder_lookup || artifact.circuit.total_tables_size == endOffset do
    throw "non-decoder setup has unaccounted real rows"

/-- Parse the exported data; no Rust row formula is reconstructed in Lean. -/
def parse (source : String) : Except String Artifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "trace_len", "circuit", "program",
    "tables", "columns", "range16", "timestamp_range"]
  let artifact : Artifact ← fromJson? json
  artifact.validate
  pure artifact

end Airbender.Setup
