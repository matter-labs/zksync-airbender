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
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.UnifiedDelegation
open Airbender Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

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
  cases highControl <;> simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, abiAssignment, Tests.BigintMemory.row,
    Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (refine ⟨⟨0, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨262144, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1310720, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1312768, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1316864, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1325056, by decide +kernel⟩, ?_⟩; decide +kernel)

private theorem abiTimestamps (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl)) Bigint.importedConstraintsTimestampLookups := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, abiAssignment, Tests.BigintMemory.row]
  all_goals decide +kernel

end Tests.UnifiedDelegation
