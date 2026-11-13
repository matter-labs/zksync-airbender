module
public import Tests.DelegationCaller
public import Tests.BigintMemory
public import Tests.DelegationOperationEffects
public import Proven.UnifiedReduced.Delegation
public import Proven.UnifiedReduced.ControlContext
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.WordMemory.Output
public import Human.Trace.UnifiedReduced.PreparedRoundWindows
public import Proven.Arithmetic.ShiftAssembly
public import Proven.Arithmetic.WordBytes
public import Proven.Arithmetic.WordRotation
public import Proven.Trace.CompositionCore
public import Proven.Trace.ROMView
public import Proven.Trace.WindowCounts
public import Proven.UnifiedReduced.WordROM
public import Human.Circuits.UnifiedReduced.Tables.Setup
public import Proven.Bigint.WitnessCheck
public import Proven.KernelRfl

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
  else if column = 1 then 5 else NonVacuous.Bigint.row column
private theorem abiCore (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl))
    (Bigint.importedConstraints Bigint.setupTable) := by
  cases highControl <;> exact Bigint.holds_of_check (by kernel_rfl)

private theorem abiTimestamps (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl)) Bigint.importedConstraintsTimestampLookups := by
  cases highControl <;> exact Bigint.timestamps_of_check (by kernel_rfl)

end Tests.UnifiedDelegation
