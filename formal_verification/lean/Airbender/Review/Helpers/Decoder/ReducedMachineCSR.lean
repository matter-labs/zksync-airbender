import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.CSRDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false
/-- Full original public sparse/padded CSR decoder membership. No per-row mask,
    source, request, privileged execution or native/physical setup identity. -/
def CSRDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup CSRMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery
end Airbender.ReducedMachine.Native
