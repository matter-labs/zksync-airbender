import Airbender.Proofs.Keccak.SplitNativeSetup
import Airbender.Proofs.Keccak.SplitParityCallExecution
import Airbender.Proofs.Keccak.SplitThetaCallExecution
import Airbender.Proofs.Keccak.SplitChiCallExecution

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Dispatch an actual native split row to its original complete Sail call.
The exact initialized history and read observations remain explicit. -/
theorem native_call_executes (cached : Bool) (row : Row babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached fixedSetup))
    (active : row.assignment (row.columns cached).execute = 1)
    (index : Fin 361) {before after : State} (arguments : ArgumentsAt index.val before)
    (boundedReads : ∀ port ∈ row.ports cached, (readToken row.assignment port).word.Bounded)
    {cells : List Cell} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((row.memorySteps cached).map transferEvent))
    (observed : ∀ port ∈ row.ports cached, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before) :
    Call.Executes row.kind before after := by
  rcases row with ⟨kind, w⟩
  have executing : w 0 = 1 := by cases kind <;> cases cached <;> exact active
  cases kind with
  | columnParity =>
    apply parity_call_executes cached w _ executing index arguments boundedReads history permutation observed
    cases cached <;> exact holds
  | thetaRho =>
    apply theta_call_executes cached w _ executing index arguments boundedReads history permutation observed
    cases cached <;> exact holds
  | chi5 =>
    apply chi5_call_executes cached w _ executing index arguments _ history permutation observed
    · cases cached <;> exact holds
    · exact boundedReads _ (chi5_call_ports_present cached w).2.1

end Airbender.Keccak.Split.Native.Proofs
