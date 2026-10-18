import Airbender.Review.Helpers.Context.JumpBranchSlt
import Airbender.Review.Circuits.JumpBranchSlt.Decoder

namespace Airbender.JumpBranchSlt
open Trace

/-- Complete sparse/padded membership at the actual imported native query.
    Public byte construction and native constraints derive field meanings. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : Data p JumpBranchSltFamily)
    (setup : SparseDecoderSetup Unit) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.JumpBranchSlt
