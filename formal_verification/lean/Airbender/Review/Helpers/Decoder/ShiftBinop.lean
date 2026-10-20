import Airbender.Review.Helpers.Context.ShiftBinop
import Airbender.Review.Circuits.ShiftBinop.Decoder

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Trace

/-- Complete sparse/padded membership at the actual imported native query.
    Public byte construction and native constraints derive field meanings. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : Data p ShiftBinopFamily)
    (setup : SparseDecoderSetup Operation) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.ShiftBinop
