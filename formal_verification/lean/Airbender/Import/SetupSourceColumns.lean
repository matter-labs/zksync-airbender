import Airbender.Import.SetupSourceData

namespace Airbender.Setup.SourceData
open Lean

/-- Keep every RLE block in its retained column order. -/
def columnJson (column : Column) : Json :=
  Json.mkObj [("blocks", .arr (column.blocks.map blockJson))]

/-- Keep every physical column in its retained array position. -/
def columnsJson (columns : Array Column) : Json := .arr (columns.map columnJson)

end Airbender.Setup.SourceData
