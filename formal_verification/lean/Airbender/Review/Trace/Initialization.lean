import Airbender.Review.Trace.History
import Airbender.Proofs.Trace.PublicImage

namespace Airbender.Trace

/-- Native v2 ADD/SUB logical memory initialized from actual public Sail reads.
    Public constructors replace all initial clock/value and address-uniqueness
    premises. Every imported read uses its newest preceding write in a complete
    Clean online-consistent history. Decoding and whole Sail execution remain separate. -/
theorem public_image_memory_soundness {trace : Data mersenne31Modulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace) :
    (∃ history, MemoryHistory trace history) ∧
      ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  native_memory_soundness accepted (Proofs.image_clock_boundary (by decide) inputs)
    (Proofs.image_unique inputs.image inputs.domain)

end Airbender.Trace
