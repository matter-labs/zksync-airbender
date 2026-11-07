import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.UnifiedDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- FULL original sparse/padded public membership. This does not identify its
    arbitrary logical source image with native fixed ROM or physical export. -/
def UnifiedDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup UnifiedMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.ReducedMachine.Native
