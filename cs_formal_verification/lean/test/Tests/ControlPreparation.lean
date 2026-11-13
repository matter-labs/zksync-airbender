module
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.WordMemory.Output
public import Human.Trace.UnifiedReduced.PreparedRoundWindows
public import Proven.AddSub
public import Proven.Arithmetic.ShiftAssembly
public import Proven.Arithmetic.SignExtend
public import Proven.Arithmetic.WordBytes
public import Proven.Arithmetic.WordRotation
public import Proven.Blake2G.CallGroups
public import Proven.Blake2G.PhysicalWords
public import Proven.Delegation.NativeSegments
public import Proven.Delegation.RequestWindows
public import Proven.Delegation.SharedOperations
public import Proven.Delegation.WorkerProjection
public import Proven.JumpBranchSlt.Branch
public import Proven.JumpBranchSlt.Jump
public import Proven.Keccak.CallPermutation
public import Proven.Trace.BytePorts
public import Proven.Trace.CompositionCore
public import Proven.Trace.ROMView
public import Proven.Trace.WindowCounts
public import Proven.UnifiedReduced.ControlContext
public import Proven.UnifiedReduced.Delegation
public import Proven.UnifiedReduced.WordROM

@[expose] public section

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768

private def register (mode : Fin 3) : BitVec 5 := if mode.val = 2 then 10 else 12
private def low (mode : Fin 3) : Nat := if mode.val = 0 then 128 else 0
private def high (mode : Fin 3) : Nat := if mode.val = 1 then 8 else 0

theorem overlapping_or_unaligned_sequences_rejected :
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 12), (8, 12)] ∧
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 6), (8, 12)] := by
  simp [UnifiedReduced.Caller.WindowsOrdered]

end Tests.ControlPreparation
