import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.JumpDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Complete sparse/padded public decoder membership for the selected jump profile.
    This is a separate logical decoder boundary, not native fixed ROM equivalence
    or physical preprocessing enforcement. -/
def JumpDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup JumpMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.ReducedMachine.Native
