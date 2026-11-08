module
public import Slop.Delegation.Requests
public import Slop.AddSub.Selectors
public import Human.Helpers.Delegation.CallerRequests

@[expose] public section

namespace Airbender.Delegation.Requests.Proofs
open Trace
set_option warningAsError true

theorem caller_tokens [Fact p.Prime] {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      AddSub.importedConstraints) (selected : w 17 = 1) :
    readToken w AddSub.importedConstraintsMemoryPorts[1] = (caller w).empty ∧
    writeToken AddSub.importedConstraintsTraceColumns w AddSub.importedConstraintsMemoryPorts[1] =
      (caller w).issued ∧ w 33 = 0 ∧ w 34 = 0 := by
  obtain ⟨lo, hi, timeLo, timeHi, resultLo, resultHi⟩ := AddSub.Proofs.delegation_zeroes constraints selected
  simp [caller, callerPort, AddSub.importedConstraintsDecoderColumns, Request.issued, Request.empty, Request.token, AddSub.importedConstraintsMemoryPorts,
    AddSub.importedConstraintsTraceColumns, readToken, writeToken, MemoryAddress.code,
    MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
    rawPair, lo, hi, timeLo, timeHi, resultLo, resultHi]
  decide

end Airbender.Delegation.Requests.Proofs
