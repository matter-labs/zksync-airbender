import Airbender.Import.SetupEmbed
import Airbender.Review.Compiler.LookupOperands

namespace Airbender.Compiler
set_option warningAsError true

/-- Setup coordinates are semantic inputs to the compiler. Table functions and
program contents are interpreted separately; their values are not obtained
from lookup gate operands. -/
inductive SourceSetupColumn where
  | generic : Nat → SourceSetupColumn
  | range16
  | timestamp
  deriving DecidableEq

def SourceSetupColumn.address : SourceSetupColumn → GKRAddress
  | .generic column => .Setup column
  | .range16 => .VirtualSetup .RangeCheck16Bits
  | .timestamp => .VirtualSetup .RangeCheckTimestamp

structure SourceLookupSetupRow where
  fields : List Source.BaseField
  multiplicity : Source.BaseField

/-- Actual physical lookup columns, with a common native row domain. Table
contents remain literal imported values rather than compiler query operands. -/
structure MaterializedLookupSetup (width : Nat) where
  imported : Setup.Imported width
  rangeDomain : imported.range16.length = imported.data.length
  timestampDomain : imported.timestampRange.length = imported.data.length

def MaterializedLookupSetup.value (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) : SourceSetupColumn → Source.BaseField
  | .generic column => (((model.imported.data.row row).toArray[column]?).getD 0 : Source.BaseField)
  | .range16 => ((model.imported.range16.row
      ⟨row.val, by rw [model.rangeDomain]; exact row.isLt⟩)[0] : Source.BaseField)
  | .timestamp => ((model.imported.timestampRange.row
      ⟨row.val, by rw [model.timestampDomain]; exact row.isLt⟩)[0] : Source.BaseField)

def MaterializedLookupSetup.fields (model : MaterializedLookupSetup width) (columns : List SourceSetupColumn)
    (row : Fin model.imported.data.length) : List Source.BaseField := columns.map (model.value row)

def MaterializedLookupSetup.row (model : MaterializedLookupSetup width) (columns : List SourceSetupColumn)
    (row : Fin model.imported.data.length) (multiplicity : Source.BaseField) : SourceLookupSetupRow :=
  ⟨model.fields columns row, multiplicity⟩

def MaterializedLookupSetup.Contains (model : MaterializedLookupSetup width) (columns : List SourceSetupColumn)
    (fields : List Source.BaseField) : Prop := ∃ row, fields = model.fields columns row

end Airbender.Compiler
