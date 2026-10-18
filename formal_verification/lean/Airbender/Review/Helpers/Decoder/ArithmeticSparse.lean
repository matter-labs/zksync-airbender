import Airbender.Review.Helpers.Decoder.SparseSetup

namespace Airbender.AddSub
open Trace

abbrev sparseDecoderSetupImage := sparseDecoderSetupImageWith decoderFields

/-- Membership retains every indexed unsupported slot and the full native tail.
    Accepted native mask equations exclude these slots during proof assembly. -/
def SparseDecoded {p : Nat} [Fact p.Prime] (trace : Data p)
    (setup : SparseDecoderSetup Family) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.AddSub
