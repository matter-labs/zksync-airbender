import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Review.Circuits.ReducedMachine.SupportedDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Complete original public sparse/padded membership for mixed selected shift
    arithmetic, bitwise, comparison and branch rows. Native fixed-ROM/physical setup fidelity stays separate. -/
def SupportedDecodedTrace {p : Nat} [Fact p.Prime] (trace : Data p NativeReducedFamily)
    (setup : SparseDecoderSetup SupportedMode) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

/-- The public original program requires readable misa only when it contains a
    retained branch. Its value is unrestricted; local reads follow from history. -/
def SupportedISA (setup : SparseDecoderSetup SupportedMode)
    (initial : Reference.RiscV.Sail.State) : Prop :=
  (∃ entry ∈ setup.program, ∃ args, entry.instruction = .BTYPE args) →
    ∃ value, initial.regs.get? .misa = some value

end Airbender.ReducedMachine.Native
