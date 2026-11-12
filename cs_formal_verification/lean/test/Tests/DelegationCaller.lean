module
public import Proven.Delegation.Requests
public import Proven.Trace.Timestamps
public import Human.Circuits.Bigint.Memory
public import Proven.Bigint.Addresses
public import Proven.Final.Circuits.Blake2G.Theorems
public import Human.Trace.Workers.Blake2G.WorkVector
public import Proven.Blake2G.CallGroups
public import Proven.Blake2G.PhysicalWords
public import Proven.Delegation.NativeSegments
public import Proven.Delegation.RequestWindows
public import Proven.Delegation.SharedOperations
public import Proven.Delegation.WorkerProjection
public import Proven.JumpBranchSlt.Branch
public import Proven.JumpBranchSlt.Jump
public import Proven.Keccak.CallPermutation
public import Proven.MulDiv.Values
public import Proven.SubwordMemory.Values
public import Proven.CleanCore.Circuit.Operations
public import Proven.AddSub.ArtifactChecks

@[expose] public section

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
