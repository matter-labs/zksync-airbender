import Airbender.Import.SetupSourceData

namespace Airbender.Setup.SourceData
open Lean

/-- Keep every RLE block in its retained column order. -/
def columnJson (column : Column) : Json :=
  Json.mkObj [("blocks", .arr (column.blocks.map blockJson))]

/-- Keep every physical column in its retained array position. -/
def columnsJson (columns : Array Column) : Json := .arr (columns.map columnJson)

def blockValues : Block → Array Nat
  | .affine _ _ _ => #[]
  | .dense values | .periodic _ _ values => values

/-- Keep the original block header and supply its array value separately. -/
def blockArrayTemplate : Block → Json → Json
  | block@(.affine _ _ _), _ => blockJson block
  | .dense _, values => Json.mkObj [("kind", .str "dense"), ("values", values)]
  | .periodic repetitions stride _, values => Json.mkObj [
      ("kind", .str "periodic"), ("repetitions", .num ⟨repetitions, 0⟩),
      ("stride", .num ⟨stride, 0⟩), ("values", values)]

end Airbender.Setup.SourceData
