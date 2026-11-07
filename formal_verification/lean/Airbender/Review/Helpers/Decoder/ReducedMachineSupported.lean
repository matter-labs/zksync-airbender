import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.SupportedDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Complete original public sparse/padded membership for mixed selected shift
    arithmetic, bitwise and comparison rows. Native fixed-ROM/physical setup fidelity stays separate. -/
def SupportedDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup SupportedMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.ReducedMachine.Native
