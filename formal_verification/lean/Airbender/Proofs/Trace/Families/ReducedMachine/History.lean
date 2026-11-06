import Airbender.Review.Helpers.Context.ReducedMachine
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.ReducedMachine.NativeTimestamp
import Airbender.Proofs.Mersenne31

namespace Airbender.Trace.Proofs
set_option autoImplicit false

/-- The v2 regenerated combined reduced artifact discharges the existing shared clock contract.
    No per-row bound, alignment or prior-clock premise is introduced. -/
instance {p : Nat} [Fact p.Prime] : ClockLaws NativeReducedFamily p where
  finalBound rom row h := by
    cases row with
    | mk family w =>
      cases family
      exact ReducedMachine.NativeClockProofs.final_clock_bound h
  advance hp rom row h bound := by
    cases row with
    | mk family w =>
      cases family
      exact ReducedMachine.NativeClockProofs.clock_advance hp h bound
  portsClocks row := by
    cases row with
    | mk family w => cases family; exact ReducedMachine.NativeClockProofs.memory_clocks
  offsets row := by
    cases row with
    | mk family w => cases family; exact ReducedMachine.NativeClockProofs.memory_offsets
  effects hp rom row h inputs := by
    cases row with
    | mk family w =>
      cases family
      exact ReducedMachine.NativeClockProofs.clock_effects hp h inputs

/-- Construct complete logical memory history and latest reads from public seeds. -/
theorem native_reduced_image_memory {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace) :
    (∃ history, MemoryHistory trace history) ∧
      ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  ⟨Trace.Proofs.native_memory_history (by decide) accepted
      (Trace.Proofs.image_clock_boundary (by decide) inputs)
      (Trace.Proofs.image_unique inputs.image inputs.domain),
    Trace.Proofs.latest_reads (by decide) accepted
      (Trace.Proofs.image_clock_boundary (by decide) inputs)
      (Trace.Proofs.image_unique inputs.image inputs.domain)⟩

/-- Public initialization and actual native matching derive all clocks and the
    terminal step count; local clock values and chronology are not inputs. -/
theorem native_reduced_image_clocks {trace : Data mersenne31Modulus NativeReducedFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace) :
    (∀ row ∈ trace.rows, ClockInputs row.columns row.assignment) ∧
      (∀ row ∈ trace.rows, ClockEffects row.columns row.assignment) ∧
      (timeOfPair trace.terminal.timestamp).value =
        (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length := by
  have boundary := image_clock_boundary (by decide) inputs
  exact ⟨clock_inputs (by decide) accepted boundary,
    trace_clocks (by decide) accepted boundary,trace_terminal_clock (by decide) accepted boundary⟩

end Airbender.Trace.Proofs
