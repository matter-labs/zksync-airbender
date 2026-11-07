import Airbender.Proofs.Keccak.SplitNativeWordBounds
import Airbender.Proofs.Keccak.SplitMemory
import Airbender.Proofs.Trace.TransferBounds

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Native split rows satisfy the raw write-bound rule inside an arbitrary
combined memory pool. The ambient time induction supplies earlier read bounds. -/
theorem native_write_rule (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (ambient : Transfer.Data babyBearModulus)
    (member : ∀ source ∈ row.ports cached,
      (readToken row.assignment source, row.writeToken cached source) ∈ ambient.steps)
    (port : MemoryPort) (present : port ∈ row.ports cached)
    (earlierReads : ∀ previous ∈ ambient.steps,
      (timeOfPair previous.2.time).value ≤ (timeOfPair (row.writeToken cached port).time).value →
        previous.1.word.Bounded) :
    (row.writeToken cached port).word.Bounded := by
  apply native_write_words_bounded cached row holds active _ port present
  intro source included
  apply earlierReads _ (member source included)
  have equal : (row.writeToken cached source).time = (row.writeToken cached port).time := by
    simp only [Row.writeToken, port_offset cached row included, port_offset cached row present]
  rw [equal]

end Airbender.Keccak.Split.Native.Proofs
