import Slop.Delegation.Requests
import Slop.Trace.Timestamps
import Slop.Bigint.Claims
import Slop.Blake2G.Claims
import Slop.Blake2Round.Claims
import Slop.Delegation.MixedClocks
import Slop.Delegation.RequestWindows
import Slop.Delegation.SharedOperations
import Slop.Delegation.WorkerProjection
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.Keccak.Claims
import Slop.MulDiv.Values
import Slop.ShiftBinop.Ports
import Slop.SubwordMemory.Values
import Slop.Trace.Family.Values

namespace Tests.DelegationCaller
open Airbender Delegation Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768

def assignment (family : Delegation.Family) (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 19 then 4
  else if column = 21 then 8
  else if column = 4 ∨ column = 17 ∨ column = 42 ∨ column = 43 ∨ column = 44 then 1
  else if column = 6 then Requests.csr family else 0

theorem satisfies (family : Delegation.Family) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment family))
      AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · cases family <;> decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals cases family <;> decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases family <;> decide +kernel

theorem request_address (family : Delegation.Family) :
    (Requests.caller (assignment family)).csr = Requests.csr family ∧
      31 < (Requests.caller (assignment family)).csr := by
  cases family <;> decide +kernel

end Tests.DelegationCaller
