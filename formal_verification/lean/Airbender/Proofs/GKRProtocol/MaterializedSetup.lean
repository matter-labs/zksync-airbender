import Airbender.Review.Compiler.Setup
import Airbender.Import.SetupEmbed
import Airbender.Proofs.GKRProtocol.TableLayout

namespace Airbender.Compiler
set_option warningAsError true

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
