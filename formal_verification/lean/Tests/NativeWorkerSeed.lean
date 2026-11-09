import Airbender.Review.Trace.Families.ReducedMachine.WorkerSeedTheorems

namespace Airbender.Tests.NativeWorkerSeed
open Airbender.NativeWorkerSeedProofs Airbender.NativeWorkerSeed
open Airbender.NativeDelegationSupport Airbender.NativeSparseMain
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem actual_ram_descriptor : (keyDescriptor (1 : Fin 43)).location = .indirect #v[2,3] 0 := ram_descriptor

theorem every_ram_read (w : Nat → F) :
    (Nat.unpair (Airbender.NativeWorkerClockProgress.readToken w 1).address).1 = 1 := ram_space w

theorem every_register_seed (index : BitVec 5) :
    (Nat.unpair (Trace.Cell.register index).addressCode).1 = 0 := register_space index

theorem zero_ram_is_not_x0 :
    Airbender.NativeMemoryTokens.encodeAddress (⟨0,0,0⟩ : MemoryKeyAddress) ≠
      (Trace.Cell.register 0).addressCode := by decide +kernel

theorem original_padding_record : Airbender.NativeInitializationLedger.paddingRow NativeSparseMainProofs.original = true := by decide +kernel

theorem idle_padding_record : Airbender.NativeInitializationLedger.paddingRow NativeSparseMainProofs.idle = true := by decide +kernel

/-- Reference observation only, with NO acceptance claim. A raw time changes the
    padding test even though BOTH address limbs remain zero. -/
def teardownTime (column : Nat) : F := if column = 131 then 1 else 0

theorem nonzero_time_not_padding : Airbender.NativeInitializationLedger.paddingRow teardownTime = false := by decide +kernel

theorem teardown_address_still_zero : teardownTime 126 = 0 ∧ teardownTime 127 = 0 := by decide +kernel

theorem repeated_positions_count :
    weightAt ([0,1,0,2].map fun i : Nat => if i = 0 then (1 : F) else 0) (fun _ => (0 : Nat)) id 0 = 2 := by decide +kernel

theorem absent_position_count :
    weightAt ([1,2].map fun i : Nat => if i = 0 then (1 : F) else 0) (fun _ => (0 : Nat)) id 0 = 0 := by decide +kernel

theorem colliding_idle_key_kept :
    weightAt ([0,1,2].map fun i : Nat => if i = 0 then (1 : F) else 0) (fun _ => (0 : Nat)) id 0 = 1 := by decide +kernel

theorem first_source_weight :
    weightAt ((List.range (callerAuxiliaryLayout.traceLength-1)).map (rows NativeSparseMainProofs.original ⟨0,by decide +kernel⟩))
      callerKey (fun w => w 92) (callerKey NativeSparseMainProofs.original) = 1 := source_weight ⟨0,by decide +kernel⟩

theorem final_source_weight :
    weightAt ((List.range (callerAuxiliaryLayout.traceLength-1)).map (rows NativeSparseMainProofs.original ⟨8388606,by decide +kernel⟩))
      callerKey (fun w => w 92) (callerKey NativeSparseMainProofs.original) = 1 := source_weight ⟨8388606,by decide +kernel⟩

theorem all_source_padding (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    Airbender.NativeInitializationLedger.paddingRow (rows NativeSparseMainProofs.original position i) = true := source_padding position i

theorem allowed_counts_stay_nonzero :
    (1 : F) ≠ 0 ∧ (256 : F) ≠ 0 ∧ (257 : F) ≠ 0 ∧ (8192 : F) ≠ 0 := by decide +kernel

theorem complete_main_retained {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    (withMain main proof).initialization.main = main := withMain_memory main proof

theorem six_scalar_observations_retained {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    (withMain main proof).initialization.base = proof.initialization.base ∧
    (withMain main proof).initialization.witness = proof.initialization.witness ∧
    (withMain main proof).initialization.setup = proof.initialization.setup ∧
    (withMain main proof).initialization.scalarPolynomial = proof.initialization.scalarPolynomial ∧
    (withMain main proof).initialization.scalarOmega = proof.initialization.scalarOmega ∧
    (withMain main proof).initialization.values = proof.initialization.values := withMain_scalar main proof

theorem four_decoder_observations_retained {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    (withMain main proof).witness = proof.witness ∧ (withMain main proof).setup = proof.setup ∧
    (withMain main proof).polynomial = proof.polynomial ∧ (withMain main proof).omega = proof.omega := withMain_decoder main proof

theorem complete_copy_weight {R : Type} [Field R] (proof : Airbender.NativeMainDecoder.Proof R) (countWord : BitVec 32)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (same : proof.initialization.main.memory.rows = rows NativeSparseMainProofs.original position) :
    Airbender.NativeDelegationKeyAccounting.callerWeight (Airbender.NativeInactiveGlobal.copies proof countWord).main.proofs
      (callerKey NativeSparseMainProofs.original) = (countWord.toNat : F) := copy_weight proof countWord position same

theorem complete_copy_padding {R : Type} [Field R] (proof : Airbender.NativeMainDecoder.Proof R) (countWord : BitVec 32)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (same : proof.initialization.main.memory.rows = rows NativeSparseMainProofs.original position) :
    ∀ w ∈ callerRows (Airbender.NativeInactiveGlobal.copies proof countWord).main.proofs,
      Airbender.NativeInitializationLedger.paddingRow w = true := copy_padding proof countWord position same

end Airbender.Tests.NativeWorkerSeed
