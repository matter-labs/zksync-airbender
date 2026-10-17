import Airbender.Proofs.Trace.Families.WordMemory.ProjectedInputs

namespace Airbender.WordMemory
open Arithmetic Trace

/-- Public initialization/setup and native matching derive effective addresses,
    bounded aligned PCs, RV32 successors and native clock/port order. No per-row
    numerical interfaces are supplied. Actual Sail execution remains separate. -/
theorem public_native_effects {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (inputs : ImageBoundary trace before cells)
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows,
      (addressWord row.assignment).toBitVec =
        (sourceWord row.assignment).toBitVec + (immediateWord row.assignment).toBitVec ∧
      row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4 ∧
      ClockEffects row.columns row.assignment :=
  Proofs.image_native_effects inputs image accepted decoded

/-- The separate architectural/shadow initializer derives the same complete
    native numerical effects without any Sail shadow reads or per-row answers. -/
theorem public_projected_native_effects {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (inputs : ShadowImageBoundary trace before cells seeds)
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows,
      (addressWord row.assignment).toBitVec =
        (sourceWord row.assignment).toBitVec + (immediateWord row.assignment).toBitVec ∧
      row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4 ∧
      ClockEffects row.columns row.assignment :=
  Proofs.projected_native_effects inputs image accepted decoded

end Airbender.WordMemory
