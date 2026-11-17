module
public import Lean

@[expose] public section

/- Compressed native setup columns, as written by `prover/src/gkr/prover/setup_artifact.rs`
   (`ColumnBlock`, `value_at`). Proofs consume only what `decode` returns. -/

namespace Airbender.Import.Setup

open Lean

inductive Block where
  | affine (length : Nat) (first : Int) (step : Int)
  | dense (values : Array Int)
  | periodic (repetitions : Nat) (stride : Int) (values : Array Int)
  deriving Repr, Inhabited, BEq

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

/-- The native setup fields used by the model. -/
structure SetupData where
  /-- The number of rows of every column. -/
  traceLen : Nat
  /-- The generic lookup columns, in native column order. -/
  columns : Array (List Block)
  /-- The virtual 16-bit range column. -/
  range16 : List Block
  /-- The virtual timestamp range column. -/
  timestampRange : List Block
  deriving Inhabited

/-- `rows` gives the generic columns of `data` on every row of its trace domain, in native
    column order. -/
def SetupData.Rows (data : SetupData) {width : Nat} (rows : Nat → Vector Int width) : Prop :=
  data.columns.size = width ∧ ∀ index < data.traceLen, ∀ column : Fin width,
    decode (data.columns.getD column.val []) index = (rows index)[column]

end Airbender.Import.Setup
