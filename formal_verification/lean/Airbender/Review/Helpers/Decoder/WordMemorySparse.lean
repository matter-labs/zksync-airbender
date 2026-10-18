import Airbender.Review.Helpers.Decoder.WordMemory
import Airbender.Review.Helpers.Decoder.SparseSetup

namespace Airbender.WordMemory
open Trace

abbrev sparseDecoderSetupImage := sparseDecoderSetupImageWith decoderFields

def SparseDecoded {p : Nat} [Fact p.Prime] (trace : Data p WordMemoryFamily)
    (setup : SparseDecoderSetup WordMemoryFamily) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.WordMemory
