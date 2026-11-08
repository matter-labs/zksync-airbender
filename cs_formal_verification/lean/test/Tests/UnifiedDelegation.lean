module
public import Tests.DelegationCaller
public import Tests.BigintMemory
public import Tests.DelegationOperationEffects
public import Slop.UnifiedReduced.Delegation
public import Slop.UnifiedReduced.ControlContext
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.WordMemory.Output
public import Human.Trace.UnifiedReduced.PreparedRoundWindows
public import Slop.Arithmetic.ShiftAssembly
public import Slop.Arithmetic.WordBytes
public import Slop.Arithmetic.WordRotation
public import Slop.Trace.CompositionCore
public import Slop.Trace.ROMView
public import Slop.Trace.WindowCounts
public import Slop.UnifiedReduced.WordROM
public import Human.Circuits.UnifiedReduced.Tables.Setup
public import Slop.Bigint.WitnessCheck
public import Slop.KernelRfl

@[expose] public section

namespace Tests.UnifiedDelegation
open Airbender Trace Arithmetic
set_option warningAsError true

private theorem endpoint_permutation {start finish target : List (MemoryToken babyBearModulus)}
    {steps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    (matching : (start ++ steps.map Prod.snd).Perm (finish ++ steps.map Prod.fst))
    (expected : (start ++ steps.map Prod.snd).Perm (target ++ steps.map Prod.fst)) : finish.Perm target :=
  (List.perm_append_right_iff _).mp (matching.symm.trans expected)

private def abiAssignment (highControl : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 55 ∨ column = 56 ∨ column = 59 then (if highControl then 1 else 0)
  else if column = 66 then 0
  else if column = 1 then 5 else Tests.BigintMemory.row column
private theorem abiCore (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl))
    (Bigint.importedConstraints Bigint.setupTable) := by
  cases highControl <;> exact Bigint.holds_of_check (by kernel_rfl)

private theorem abiTimestamps (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl)) Bigint.importedConstraintsTimestampLookups := by
  cases highControl <;> exact Bigint.timestamps_of_check (by kernel_rfl)

end Tests.UnifiedDelegation
