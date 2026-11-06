import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.Mersenne31

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
open Trace

/-- Actual public seed reads and native matching yield complete Clean memory
    consistency and newest preceding reads for all three actual native v2 reduced ports.
    Readonly alias refreshes and the actual masked destination write remain in
    matching. Word bounds and original Sail cell/instruction execution are separate. -/
theorem public_memory_soundness {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace) :
    (∃ history, MemoryHistory trace history) ∧
      ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  Trace.Proofs.native_reduced_image_memory inputs accepted

/-- Public seeds and native matching derive local/prior clocks, strict access
    order and exactly four terminal ticks per participating native row. -/
theorem public_clock_soundness {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace) :
    (∀ row ∈ trace.rows, ClockInputs row.columns row.assignment) ∧
      (∀ row ∈ trace.rows, ClockEffects row.columns row.assignment) ∧
      (timeOfPair trace.terminal.timestamp).value =
        (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length :=
  Trace.Proofs.native_reduced_image_clocks inputs accepted

end Airbender.ReducedMachine.Native
