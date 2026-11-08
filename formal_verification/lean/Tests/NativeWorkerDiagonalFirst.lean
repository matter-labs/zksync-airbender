import Airbender.Review.Trace.Families.ReducedMachine.WorkerDiagonalFirstTheorems
import Tests.NativeWorkerColumnG

namespace Airbender.Tests.NativeWorkerDiagonalFirst
open Airbender.NativeWorkerDiagonalFirst Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Exact four source call-site permutations; pure finite reference only. -/
theorem source_permutations (diagonal component : Fin 4) :
    (sourceColumn diagonal component).val = (#v[#v[0,1,2,3],#v[1,2,3,0],#v[2,3,0,1],#v[3,0,1,2]] : Vector (Vector Nat 4) 4)[diagonal][component] := by
  fin_cases diagonal <;> fin_cases component <;> decide +kernel

theorem pair97_maximum : (511+512*127 : Nat) = 65535 := by decide +kernel

private def chunks (column : Nat) : F :=
  if column=310 then 1 else if column=311 then 2 else if column=312 then 3 else if column=313 then 4 else 0
/-- Distinct chunk data only, not an accepted native witness. -/
theorem distinct_b_chunks : bLimb chunks 0 0 = 1538 ∧ bLimb chunks 0 1 = 516 ∧
    Airbender.NativeWorkerFirstG.pack (bLimb chunks 0 0) (bLimb chunks 0 1) = (0x02040602 : BitVec 32) := by decide +kernel

theorem first_steps_vector :
    (0xFFFF0001 : BitVec 32)+0x12345678+0xFFFFFFFF = 0x12335678 ∧
      (((0x89ABCDEF : BitVec 32) ^^^ (0x12335678 : BitVec 32)).rotateRight 16) = 0x9B979B98 := by decide +kernel

/-- Old complete LOCAL BODY; its zero-pointer aliases stay visible. -/
theorem full_local_first : LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_diagonal_first Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_a_sums (diagonal : Fin 4) (limb : Fin 2) :
    sumLimb Airbender.Blake2Worker.PositiveRow.assignment diagonal limb = 0 := by
  fin_cases diagonal <;> fin_cases limb <;>
    simp [sumLimb,inputLimb,columnLimb,sourceColumn,bLimb,carry,
      Airbender.NativeWorkerSecondAD.sumLimb,Airbender.NativeWorkerSecondAD.bInput,Airbender.NativeWorkerSecondAD.carry,
      Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,
      Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns,
      Airbender.NativeWorkerSchedule.selected,Airbender.Blake2Worker.PositiveRow.assignment]

theorem zero_d_outputs (diagonal : Fin 4) : dAfter Airbender.Blake2Worker.PositiveRow.assignment diagonal = 0 := by
  fin_cases diagonal <;> decide +kernel

theorem all_inputs {w : Nat → F} (effects : Airbender.NativeWorkerDiagonalFirst.RowEffects w) :
    ∀ diagonal component : Fin 4, ∀ limb : Fin 2, (inputLimb w diagonal component limb).val < 65536 := effects.inputs

theorem all_routed {w : Nat → F} (effects : Airbender.NativeWorkerDiagonalFirst.RowEffects w) :
    ∀ diagonal component : Fin 4, inputWord w diagonal component =
      (Airbender.NativeWorkerSecondCB.columnResult w (sourceColumn diagonal component))[component] := effects.routed

theorem all_carry_bits {w : Nat → F} (effects : LocalEffects w) :
    ∀ diagonal slot : Fin 4, (carryBit w diagonal slot).val ≤ 1 := effects.carries

theorem all_sum_bounds {w : Nat → F} (effects : LocalEffects w) :
    ∀ diagonal : Fin 4, ∀ limb : Fin 2, (sumLimb w diagonal limb).val < 65536 := effects.bounds

theorem encoded_carry_bounds {w : Nat → F} (effects : Airbender.NativeWorkerDiagonalFirst.RowEffects w) :
    ∀ diagonal : Fin 4, ∀ limb : Fin 2, (carry w diagonal limb).val ≤ 3 := effects.carryBounds

theorem all_additions {w : Nat → F} (effects : Airbender.NativeWorkerDiagonalFirst.RowEffects w) :
    ∀ diagonal : Fin 4, aAfter w diagonal = inputWord w diagonal 0+ inputWord w diagonal 1+
      Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩ := effects.added

theorem all_d_rotations {w : Nat → F} (effects : LocalEffects w) :
    ∀ diagonal : Fin 4, dAfter w diagonal = (inputWord w diagonal 3 ^^^ aAfter w diagonal).rotateRight 16 := effects.rotated

theorem weighted_messages_retained {w : Nat → F} (effects : Airbender.NativeWorkerDiagonalFirst.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2,
      (Airbender.NativeWorkerSchedule.selected w word limb).val = Airbender.NativeWorkerAddition.selectedNatural w word limb ∧
        Airbender.NativeWorkerAddition.selectedNatural w word limb < 655360 := effects.prior.prior.prior.prior.selected

private def corrupt (column : Nat) : F := if column=458 then 1 else Airbender.Blake2Worker.PositiveRow.assignment column

theorem corrupt_d_output_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment corrupt) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_diagonal_first holds).rotated 0
  exact (by decide +kernel : ¬ (dAfter corrupt 0 = (inputWord corrupt 0 3 ^^^ aAfter corrupt 0).rotateRight 16)) bad

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerColumnG.inactive_requests_retained
theorem complete_counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerDiagonalFirst.RowEffects w :=
  native_counted_worker_diagonal_first publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerDiagonalFirst
