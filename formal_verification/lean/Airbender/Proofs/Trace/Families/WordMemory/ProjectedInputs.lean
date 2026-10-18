import Airbender.Proofs.Trace.Families.WordMemory.Inputs
import Airbender.Proofs.Trace.Families.WordMemory.ShadowImage

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Verification

/-- Canonical architectural and shadow seeds supply the source bound; actual
    public decoding and native clocks discharge the unchanged address/PC laws. -/
theorem indexed_projected_native_effects {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} {count : Nat}
    (inputs : ShadowImageBoundary trace before cells seeds)
    (image : IndexedProgram before count setup.program)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows,
      (addressWord row.assignment).toBitVec =
        (sourceWord row.assignment).toBitVec + (immediateWord row.assignment).toBitVec ∧
      row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4 ∧
      ClockEffects row.columns row.assignment :=
  indexed_native_effects_from_bounds (shadow_clock_boundary (by decide) inputs) image accepted decoded
    (source_bound_of_reads (shadow_value_bounds (by decide) inputs accepted decoded).1)

/-- The original strict public setup shares the same initialized calculations. -/
theorem projected_native_effects {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (inputs : ShadowImageBoundary trace before cells seeds)
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows,
      (addressWord row.assignment).toBitVec =
        (sourceWord row.assignment).toBitVec + (immediateWord row.assignment).toBitVec ∧
      row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4 ∧
      ClockEffects row.columns row.assignment :=
  indexed_projected_native_effects inputs (strict_indexed_program image) accepted decoded

end Airbender.WordMemory.Proofs
