import Airbender.Review.Helpers.Context.MulDiv
import Airbender.Review.Circuits.MulDiv.Decoder

namespace Airbender.MulDiv
open Trace

/-- Complete sparse/padded membership at the actual imported native query.
    Public byte construction and native constraints derive field meanings. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : Data p MulDivFamily)
    (setup : SparseDecoderSetup Operation) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.MulDiv
