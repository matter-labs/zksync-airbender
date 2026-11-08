import Airbender.Review.Trace.Families.ReducedMachine.WorkerFirstGTheorems
import Tests.NativeWorkerInitial

namespace Airbender.Tests.NativeWorkerFirstG
open Airbender.NativeWorkerFirstG Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
open Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure two-bit encoding, not an accepted native row with carry3. -/
theorem carry_weights : carry (fun _ => 1) 0 0 = (3 : F) ∧ carry (fun _ => 1) 0 1 = (3 : F) := by decide +kernel

theorem xor_rotation_vector :
    (((0x01234567 : BitVec 32) ^^^ (0x0F1E2D3C : BitVec 32)).rotateRight 16) = (0x685B0E3D : BitVec 32) := by decide +kernel

/-- Reuse old complete LOCAL zero-control BODY; aliases remain visible. -/
theorem full_local_first_step : Airbender.NativeWorkerFirstG.RowEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_first_g_step Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_sums (column : Fin 4) (limb : Fin 2) : sumLimb Airbender.Blake2Worker.PositiveRow.assignment column limb = 0 := by
  fin_cases column <;> fin_cases limb <;>
    simp [sumLimb,observed,initialColumns,selected,carry,Airbender.Blake2Worker.PositiveRow.assignment]

theorem zero_d_input (column : Fin 4) (limb : Fin 2) : dInput Airbender.Blake2Worker.PositiveRow.assignment column limb = 0 := by
  fin_cases column <;> fin_cases limb <;>
    simp [dInput,observed,initialColumns,Airbender.Blake2Worker.PositiveRow.assignment]

theorem zero_d_output (column : Fin 4) : dAfter Airbender.Blake2Worker.PositiveRow.assignment column = 0 := by
  fin_cases column <;> decide +kernel

theorem all_carry_bits {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    ∀ column : Fin 4, ∀ slot : Fin 4, (carryBit w column slot).val ≤ 1 :=
  (native_worker_first_g_step holds).carries

theorem all_limb_bounds {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (sumLimb w column limb).val < 65536 ∧ (dInput w column limb).val < 65536 :=
  (native_worker_first_g_step holds).bounds

theorem all_d_rotations {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    ∀ column : Fin 4, dAfter w column =
      (pack (dInput w column 0) (dInput w column 1) ^^^ pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 16 :=
  (native_worker_first_g_step holds).rotated

theorem prior_control_schedule {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerSchedule.RowEffects w := (native_worker_first_g_step holds).initial.schedule

private def corrupt (column : Nat) : F := if column = 275 then 1 else Airbender.Blake2Worker.PositiveRow.assignment column

theorem corrupt_xor_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment corrupt) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_first_g_step holds).rotated 0
  exact (by decide +kernel : ¬ (dAfter corrupt 0 =
    (pack (dInput corrupt 0 0) (dInput corrupt 0 1) ^^^
      pack (sumLimb corrupt 0 0) (sumLimb corrupt 0 1)).rotateRight 16)) bad

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerInitial.inactive_requests_retained
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerFirstG.RowEffects w :=
  native_counted_worker_first_g_step publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerFirstG
