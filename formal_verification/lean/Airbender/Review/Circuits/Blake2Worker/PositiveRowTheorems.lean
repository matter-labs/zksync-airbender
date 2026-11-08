import Airbender.Proofs.Blake2Worker.NativePositiveRow

namespace Airbender.Blake2Worker.PositiveRow
open Verification Native

/-- Complete local native body: all352 equations and296 actual lookups. No
    global/source-worker acceptance, memory history or Sail effect is claimed. -/
theorem native_positive_body : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (constraints Fixed.table) := PositiveRowProofs.body

/-- Existing normalized processing conventions on the same explicit row. -/
theorem native_positive_processing : LocalProcessingAccepted assignment := PositiveRowProofs.local_processing

end Airbender.Blake2Worker.PositiveRow
