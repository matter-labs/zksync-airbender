import Airbender.Review.Helpers.Memory.PublicImage
import Airbender.Proofs.Trace.InitialImage

namespace Airbender.Trace.Proofs

/-- Public constructors discharge all initial memory/clock conditions used by
    native history recovery. No per-row clock or read-value premise is added. -/
theorem image_clock_boundary {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {trace : Data p Kind} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) : ClockBoundary trace := by
  have four : (4 : ZMod p).val = 4 := ZMod.val_natCast_of_lt hp
  obtain ⟨pc, _, initial⟩ := initial_state_source inputs.initial
  constructor
  · rw [initial]
    change (timeOfPair ((4 : ZMod p), 0)).Bounded
    simp [timeOfPair, Timestamp.Bounded, four, timestampBase]
  · rw [initial]
    change (timeOfPair ((4 : ZMod p), 0)).value % 4 = 0
    simp [timeOfPair, Timestamp.value, four]
  · exact image_clocks inputs.image

end Airbender.Trace.Proofs
