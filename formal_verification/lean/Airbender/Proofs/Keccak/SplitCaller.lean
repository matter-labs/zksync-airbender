import Airbender.Review.Helpers.Delegation.SplitCaller
import Airbender.Proofs.Keccak.SplitSchedule

namespace Airbender.Keccak.Split.Caller.Proofs
open Airbender.Keccak.Split

/-- Every blessed split call has its own Sail CSR constructor and selects the
matching native ADD/SUB delegation metadata, including selector bit seven. -/
theorem decoder_fields_instruction (kind : Split.Kind) :
    Caller.decoderFields (Caller.instruction kind) =
      some ⟨kind, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩ := by
  cases kind <;> rfl

/-- The public 361-call schedule determines the CSR at every call position. -/
theorem schedule_csr (index : Fin 361) :
    (schedule[index.val]?).map Kind.csr = some (kindAt index.val).csr := by
  rw [Split.Proofs.schedule_kind index]
  rfl

end Airbender.Keccak.Split.Caller.Proofs
