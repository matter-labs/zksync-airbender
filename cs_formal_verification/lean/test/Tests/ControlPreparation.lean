import Slop.UnifiedReduced.Completeness.Arith
import Human.Circuits.JumpBranchSlt.Jump
import Human.Circuits.UnifiedReduced.Binary
import Human.Circuits.WordMemory.Output
import Human.Trace.UnifiedReduced.PreparedRoundWindows
import Slop.AddSub
import Slop.Arithmetic.ShiftAssembly
import Slop.Arithmetic.SignExtend
import Slop.Arithmetic.WordBytes
import Slop.Arithmetic.WordRotation
import Slop.Blake2G.CallGroups
import Slop.Blake2G.PhysicalWords
import Slop.Delegation.NativeSegments
import Slop.Delegation.RequestWindows
import Slop.Delegation.SharedOperations
import Slop.Delegation.WorkerProjection
import Slop.JumpBranchSlt.Branch
import Slop.JumpBranchSlt.Jump
import Slop.Keccak.CallPermutation
import Slop.Trace.BytePorts
import Slop.Trace.CompositionCore
import Slop.Trace.ROMView
import Slop.Trace.WindowCounts
import Slop.UnifiedReduced.Binary
import Slop.UnifiedReduced.ComparisonSoundness
import Slop.UnifiedReduced.Delegation
import Slop.UnifiedReduced.WordROM

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768

private def register (mode : Fin 3) : BitVec 5 := if mode.val = 2 then 10 else 12
private def low (mode : Fin 3) : Nat := if mode.val = 0 then 128 else 0
private def high (mode : Fin 3) : Nat := if mode.val = 1 then 8 else 0
private def witness (mode : Fin 3) : UnifiedReduced.Completeness.Arith :=
  ⟨⟨0, 0, 4, 0, 0, 0, 4, 0, 0, 0⟩, 0, 0, 0, (register mode).toNat, 0, 0, 0, 0, low mode, high mode, 1, 1⟩
private def assignment (mode : Fin 3) : Nat → ZMod babyBearModulus := (witness mode).honest
private theorem valid (mode : Fin 3) : (witness mode).Valid := by
  fin_cases mode <;>
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem timestamps (mode : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment mode)) UnifiedReduced.importedConstraintsTimestampLookups := by
  fin_cases mode <;>
    exact UnifiedReduced.Completeness.Frame.timestamps
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) (witness _).columns

private def chainedWitness : UnifiedReduced.Completeness.Arith :=
  ⟨⟨4, 0, 8, 0, 5, 0, 8, 0, 6, 0⟩, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 128, 0⟩
private def chainedAssignment : Nat → ZMod babyBearModulus := chainedWitness.honest
private theorem chainedTimestamps : FlatOperation.ConstraintsHoldFlat
    (Verification.environment chainedAssignment) UnifiedReduced.importedConstraintsTimestampLookups :=
  UnifiedReduced.Completeness.Frame.timestamps
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) chainedWitness.columns

theorem chained_preparation_uses_previous_write :
    (readToken chainedAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
      (readToken chainedAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 128 := by
  decide +kernel

theorem overlapping_or_unaligned_sequences_rejected :
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 12), (8, 12)] ∧
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 6), (8, 12)] := by
  simp [UnifiedReduced.Caller.WindowsOrdered]

private def sequentialWitness (custom : Bool) (second : Bool) : UnifiedReduced.Completeness.Arith :=
  if second then
    ⟨⟨4, 0, 8, 0, 0, 0, 8, 0, 6, 0⟩, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0,
      if custom then 3 else 2, if custom then 3 else 2⟩
  else
    ⟨⟨0, 0, 4, 0, 0, 0, 4, 0, 5, 0⟩, if custom then 3 else 0, 12, 12, 12, 1, 1, 1, 1, 0, 0, 1, 1⟩
private def sequentialAssignment (custom : Bool) (second : Bool) : Nat → ZMod babyBearModulus :=
  (sequentialWitness custom second).honest
private theorem sequentialTimestamps (custom : Bool) (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (sequentialAssignment custom second)) UnifiedReduced.importedConstraintsTimestampLookups := by
  cases custom <;> cases second <;>
    exact UnifiedReduced.Completeness.Frame.timestamps
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) (sequentialWitness _ _).columns

private theorem sequential_preparation_uses_prior_aliased_add (custom : Bool) :
    (readToken (sequentialAssignment custom true) UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
    (readToken (sequentialAssignment custom true) UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = (if custom then 196611 else 131074) := by
  cases custom <;> decide +kernel

theorem arithmetic_preparation_uses_prior_aliased_add :
    (readToken ((sequentialAssignment false) true) UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
    (readToken ((sequentialAssignment false) true) UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 131074 :=
  sequential_preparation_uses_prior_aliased_add false

end Tests.ControlPreparation
