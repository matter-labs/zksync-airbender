import Lean

/- Compressed native setup columns, as written by `prover/src/gkr/prover/setup_artifact.rs`
   (`ColumnBlock`, `value_at`). Parsing and decoding are an import-layer trust boundary:
   the blocks are data, and proofs consume only what `decode` returns. -/

namespace Airbender.Import.Setup

open Lean

inductive Block where
  | affine (length : Nat) (first : Int) (step : Int)
  | dense (values : Array Int)
  | periodic (repetitions : Nat) (stride : Int) (values : Array Int)
  deriving Repr, Inhabited

namespace Block

def len : Block → Nat
  | .affine n _ _ => n
  | .dense vs => vs.size
  | .periodic r _ vs => r * vs.size

/-- `value_at` of one block, for an index inside the block. -/
def valueAt : Block → Nat → Int
  | .affine _ first step, i => first + step * i
  | .dense vs, i => vs.getD i 0
  | .periodic _ stride vs, i => vs.getD (i % vs.size) 0 + stride * (i / vs.size)

end Block

/-- Value of a column at row `i`; blocks are consumed in order, as in the Rust `value_at`. -/
def decode : List Block → Nat → Int
  | [], _ => 0
  | b :: bs, i => if i < b.len then b.valueAt i else decode bs (i - b.len)

/-- One `tables` entry of the setup JSON. -/
structure Table where
  id : Nat
  offset : Nat
  length : Nat
  width : Nat
  keyColumns : Nat
  deriving Repr, Inhabited

/-- The fields of the setup JSON that the human layer consumes. -/
structure SetupData where
  traceLen : Nat
  columns : Array (List Block)
  range16 : List Block
  timestampRange : List Block
  tables : Array Table
  deriving Inhabited

section Parse

def blockOf (j : Json) : Except String Block := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "affine" =>
    let n ← j.getObjValAs? Nat "length"
    let first ← j.getObjValAs? Int "first"
    let step ← j.getObjValAs? Int "step"
    return .affine n first step
  | "dense" =>
    let vs ← j.getObjValAs? (Array Int) "values"
    return .dense vs
  | "periodic" =>
    let r ← j.getObjValAs? Nat "repetitions"
    let stride ← j.getObjValAs? Int "stride"
    let vs ← j.getObjValAs? (Array Int) "values"
    return .periodic r stride vs
  | k => throw s!"unknown block kind {k}"

def blocksOf (j : Json) : Except String (List Block) := do
  let bs ← (← j.getObjVal? "blocks").getArr?
  bs.toList.mapM blockOf

def tableOf (j : Json) : Except String Table := do
  let id ← j.getObjValAs? Nat "id"
  let offset ← j.getObjValAs? Nat "offset"
  let length ← j.getObjValAs? Nat "length"
  let width ← j.getObjValAs? Nat "width"
  let keyColumns ← j.getObjValAs? Nat "key_columns"
  return { id, offset, length, width, keyColumns }

/-- Parse the setup JSON text. -/
def parseSetup (text : String) : Except String SetupData := do
  let j ← Json.parse text
  let version ← j.getObjValAs? Nat "version"
  if version != 1 then throw s!"unsupported setup version {version}"
  let traceLen ← j.getObjValAs? Nat "trace_len"
  let cols ← (← j.getObjVal? "columns").getArr?
  let columns : Array (List Block) ← cols.mapM blocksOf
  let range16 ← blocksOf (← j.getObjVal? "range16")
  let timestampRange ← blocksOf (← j.getObjVal? "timestamp_range")
  let tables ← (← j.getObjVal? "tables").getArr?
  let tables : Array Table ← tables.mapM tableOf
  return { traceLen, columns, range16, timestampRange, tables := tables }

end Parse

end Airbender.Import.Setup
