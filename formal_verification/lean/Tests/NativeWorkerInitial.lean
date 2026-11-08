import Airbender.Review.Trace.Families.ReducedMachine.WorkerInitialTheorems
import Tests.NativeWorkerSchedule

namespace Airbender.Tests.NativeWorkerInitial
open Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
open Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure references, not complete source-global or physical witnesses. -/
theorem configured_twist : configuredIV 0 = Nat.xor (Nat.xor iv[0] 0x01010000) 32 ∧ iv[0] = 0x6A09E667 := by decide +kernel

theorem compression_constants : compressionIV 12 = Nat.xor iv[4] 64 ∧ compressionIV 14 = Nat.xor iv[6] 0xFFFFFFFF ∧ compressionIV 0 = configuredIV 0 := by decide +kernel

theorem actual_columns : initialColumns[0] = 155 ∧ initialColumns[24] = 198 ∧ initialColumns[28] = 200 ∧ initialColumns[31] = 197 := by decide +kernel

private def withControl (high : Nat) (w : Nat → F) (column : Nat) : F := if column = 135 then high else w column

theorem no_round_preserves (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    initial (withControl 0 w) word limb = oldExtended w word limb := by
  have other : 36+4*word.val+limb.val ≠ 135 := by have := word.isLt; have := limb.isLt; omega
  simp [initial,inputBit,withControl,oldExtended,other]

theorem later_round_preserves (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    initial (withControl 16 w) word limb = oldExtended w word limb := by
  have sixteen : (16 : F).val = 16 := by decide +kernel
  have other : 36+4*word.val+limb.val ≠ 135 := by have := word.isLt; have := limb.isLt; omega
  simp [initial,inputBit,withControl,sixteen,oldExtended,other]

theorem first_normal_base (w : Nat → F) : initial (withControl 8 w) 0 0 = w 4 := by
  have eight : (8 : F).val = 8 := by decide +kernel
  simp [initial,inputBit,withControl,eight,finalBase,state]

theorem first_normal_special (w : Nat → F) :
    initial (withControl 8 w) 12 0 = w 84 ∧ initial (withControl 8 w) 14 1 = w 93 := by
  have eight : (8 : F).val = 8 := by decide +kernel
  simp [initial,inputBit,withControl,eight,oldExtended]

theorem first_normal_upper (w : Nat → F) : initial (withControl 8 w) 8 0 = limbOf 0x6A09E667 0 := by
  have eight : (8 : F).val = 8 := by decide +kernel
  simp [initial,inputBit,withControl,eight,iv]

theorem first_compression (w : Nat → F) :
    initial (withControl 12 w) 0 1 = limbOf 0x6B08E647 1 ∧
    initial (withControl 12 w) 12 0 = limbOf 0x510E523F 0 ∧
    initial (withControl 12 w) 14 1 = limbOf 0xE07C2654 1 := by
  have twelve : (12 : F).val = 12 := by decide +kernel
  simp [initial,inputBit,withControl,twelve,finalBase,configuredIV,compressionIV]

/-- Both right/left compression modes share state initialization. -/
theorem right_bit_independent (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    initial (withControl 14 w) word limb = initial (withControl 12 w) word limb := by
  have twelve : (12 : F).val = 12 := by decide +kernel
  have fourteen : (14 : F).val = 14 := by decide +kernel
  simp [initial,finalBase,inputBit,withControl,twelve,fourteen]

/-- Old full LOCAL positive BODY, including its visible zero-pointer aliases. -/
theorem full_local_initialization : Airbender.NativeWorkerInitial.RowEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_state_initialization Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_local_state (word : Fin 16) (limb : Fin 2) :
    observed Airbender.Blake2Worker.PositiveRow.assignment word limb = 0 := by
  rw [full_local_initialization.initialized]
  have other : 36+4*word.val+limb.val ≠ 740 := by have := word.isLt; have := limb.isLt; omega
  have below : ¬ 742 ≤ 36+4*word.val+limb.val := by have := word.isLt; have := limb.isLt; omega
  simp [initial,inputBit,oldExtended,Airbender.Blake2Worker.PositiveRow.assignment,other,below]

private def corrupt (column : Nat) : F := if column = 155 then 1 else Airbender.Blake2Worker.PositiveRow.assignment column

theorem corrupt_initial_rejected {setup : Table F (fields 4)} :
    ¬ FlatOperation.ConstraintsHoldFlat (environment corrupt) (constraints setup) := by
  intro holds
  have eq := (native_worker_state_initialization holds).initialized 0 0
  simp [observed,initialColumns,initial,inputBit,oldExtended,corrupt,Airbender.Blake2Worker.PositiveRow.assignment] at eq

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerSchedule.inactive_requests_retained
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerInitial.RowEffects w :=
  native_counted_worker_state_initialization publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerInitial
