import Airbender.Import.SetupEmbed
import GKRProtocol.TableLayout

namespace Airbender.Compiler
set_option warningAsError true

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

theorem MaterializedLookupSetup.value_generic (model : MaterializedLookupSetup width)
    (row : Fin model.imported.data.length) (column : Fin width) :
    model.value row (.generic column.val) = ((model.imported.data.row row)[column.val] : Source.BaseField) := by
  simp [value]

theorem MaterializedLookupSetup.row_value {R : Type} [CommRing R] (model : MaterializedLookupSetup width)
    (columns : List SourceSetupColumn) (row : Fin model.imported.data.length)
    (multiplicity : Source.BaseField) (hom : Source.BaseField →+* R) (alpha gamma : R) :
    (model.row columns row multiplicity).value hom alpha gamma =
      RationalPair.leaf (-hom multiplicity)
        (NativeLookupEncoding.linearize hom alpha (model.fields columns row) 0 0 + gamma) := rfl

end Airbender.Compiler
