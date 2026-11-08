module
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.WordMemory.Output
public import Human.Trace.UnifiedReduced.PreparedRoundWindows
public import Slop.AddSub
public import Slop.Arithmetic.ShiftAssembly
public import Slop.Arithmetic.SignExtend
public import Slop.Arithmetic.WordBytes
public import Slop.Arithmetic.WordRotation
public import Slop.Blake2G.CallGroups
public import Slop.Blake2G.PhysicalWords
public import Slop.Delegation.NativeSegments
public import Slop.Delegation.RequestWindows
public import Slop.Delegation.SharedOperations
public import Slop.Delegation.WorkerProjection
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.Keccak.CallPermutation
public import Slop.Trace.BytePorts
public import Slop.Trace.CompositionCore
public import Slop.Trace.ROMView
public import Slop.Trace.WindowCounts
public import Slop.UnifiedReduced.ControlContext
public import Slop.UnifiedReduced.Delegation
public import Slop.UnifiedReduced.WordROM

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
