module
public import Lean

@[expose] public section

/- Compressed native setup columns, as written by `prover/src/gkr/prover/setup_artifact.rs`
   (`ColumnBlock`, `value_at`), plus grid blocks (a named row formula) that the import emits
   for table regions after an exact row-by-row comparison with the JSON (`SetupEmit`).
   Parsing, that comparison and decoding are an import-layer trust boundary: the blocks are
   data, and proofs consume only what `decode` returns. -/

namespace Airbender.Import.Setup

open Lean

/-- Named row formulas of the structured (grid) blocks: the value of row `i` of the block,
    counted from the block's first row. The import emits a grid block only where every row
    of the exported JSON equals the formula (`SetupEmit`). -/
inductive GridFn where
  /-- `i / d % w`: the digit of `i` with place value `d` in base `w` (a key of an XOR,
      split or nibble table). -/
  | digit (d w : Nat)
  /-- `(i / d₁ % w) ^^^ (i / d₂ % w)`: the XOR of two digits. -/
  | xorDigits (d₁ d₂ w : Nat)
  /-- The (4+3)x(4+3) split XOR output: `(a₄ ^^^ b₄) ||| ((a₃ ^^^ b₃) <<< 4)` for
      `a₄ = i / 1024 % 16`, `a₃ = i / 128 % 8`, `b₄ = i / 8 % 16`, `b₃ = i % 8`. -/
  | xor4x3
  /-- Low byte of `(a ^^^ b) <<< s`, `a = i % 256`, `b = i / 256 % 256`, `s = i / 65536 % 8`. -/
  | rotLow
  /-- `(a ^^^ b) >>> (8 - s)`, the bits shifted out of the low byte (`a, b, s` as in `rotLow`). -/
  | rotHigh
  /-- The XOR of the five nibbles `i / 16 ^ k % 16`, `k < 5`. -/
  | xor5
  /-- Keccak chi on nibble `k` of a plane of five nibbles `n j = i / 16 ^ j % 16`:
      `n k ^^^ ((15 ^^^ n ((k + 1) % 5)) &&& n ((k + 2) % 5))`. -/
  | chi (k : Nat)
  /-- `(i % w) ^^^ t[i / w]` (`0` past the end of `t`): a byte XOR with a per-group constant. -/
  | xorTable (w : Nat) (t : Array Nat)
  deriving Repr, Inhabited, DecidableEq

namespace GridFn

/-- Nibble `j` of `i`. -/
def nibble (i j : Nat) : Nat := i / 16 ^ j % 16

/-- Value of row `i` of a grid block. -/
def eval : GridFn → Nat → Nat
  | .digit d w, i => i / d % w
  | .xorDigits d₁ d₂ w, i => i / d₁ % w ^^^ i / d₂ % w
  | .xor4x3, i => (i / 1024 % 16 ^^^ i / 8 % 16) ||| ((i / 128 % 8 ^^^ i % 8) <<< 4)
  | .rotLow, i => (i % 256 ^^^ i / 256 % 256) * 2 ^ (i / 65536 % 8) % 256
  | .rotHigh, i => (i % 256 ^^^ i / 256 % 256) / 2 ^ (8 - i / 65536 % 8)
  | .xor5, i => nibble i 0 ^^^ nibble i 1 ^^^ nibble i 2 ^^^ nibble i 3 ^^^ nibble i 4
  | .chi k, i => nibble i k ^^^ ((15 ^^^ nibble i ((k + 1) % 5)) &&& nibble i ((k + 2) % 5))
  | .xorTable w t, i => i % w ^^^ t.getD (i / w) 0

end GridFn

inductive Block where
  | affine (length : Nat) (first : Int) (step : Int)
  | dense (values : Array Int)
  | periodic (repetitions : Nat) (stride : Int) (values : Array Int)
  /-- `length` rows, row `i` holding `f.eval i`. Not part of the JSON format: the import
      emits it for a table region after checking every row against the JSON (`SetupEmit`). -/
  | grid (length : Nat) (f : GridFn)
  deriving Repr, Inhabited, BEq

namespace Block

def len : Block → Nat
  | .affine n _ _ => n
  | .dense vs => vs.size
  | .periodic r _ vs => r * vs.size
  | .grid n _ => n

/-- `value_at` of one block, for an index inside the block. -/
def valueAt : Block → Nat → Int
  | .affine _ first step, i => first + step * i
  | .dense vs, i => vs.getD i 0
  | .periodic _ stride vs, i => vs.getD (i % vs.size) 0 + stride * (i / vs.size)
  | .grid _ f, i => f.eval i

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
