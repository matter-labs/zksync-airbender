import Airbender.Review.Helpers.Context.SubwordMemory
import Airbender.Review.Circuits.SubwordMemory.Decoder

namespace Airbender.SubwordMemory
set_option autoImplicit false
open Trace

/-- Complete sparse/padded membership at the actual imported native query.
    Public byte construction and native constraints derive field meanings. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : Data p SubwordMemoryFamily)
    (setup : SparseDecoderSetup Operation) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.SubwordMemory
