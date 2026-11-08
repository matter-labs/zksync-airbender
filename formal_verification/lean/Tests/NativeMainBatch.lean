import Airbender.Review.Circuits.ReducedMachine.MainBatchTheorems

namespace Airbender.Tests.NativeMainBatch
open Airbender.NativeMainBatch
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Counter DATA ONLY. No accepted nonempty source/physical proof is supplied.
    Generic counter_iff proves all guards before replication instantiation. -/
private def repeated {R : Type} [Field R] (count : BitVec 32) (proof : Proof R) : Batch R :=
  ⟨count,Vector.replicate count.toNat proof⟩

theorem native_geometry : capacity=8388607 ∧ maxCycles=68719476736 := Airbender.NativeMainBatchProofs.geometry

theorem constructed_count {R : Type} [Field R] (batch : Batch R) : batch.proofs.length=batch.countWord.toNat :=
  Airbender.NativeMainBatchProofs.count_binding batch

theorem zero_count_rejected {R : Type} [Field R] (proof : Proof R) : ¬ CounterAccepted (repeated 0 proof) := by
  rw [Airbender.NativeMainBatchProofs.counter_iff]
  change ¬ ((0 : Nat) < 0 ∧ 0 ≤ 8192)
  decide +kernel

theorem one_count_pass {R : Type} [Field R] (proof : Proof R) : CounterAccepted (repeated 1 proof) := by
  rw [Airbender.NativeMainBatchProofs.counter_iff]
  change (0 : Nat) < 1 ∧ 1 ≤ 8192
  decide +kernel

theorem last_count_pass {R : Type} [Field R] (proof : Proof R) : CounterAccepted (repeated 8192 proof) := by
  rw [Airbender.NativeMainBatchProofs.counter_iff]
  change (0 : Nat) < 8192 ∧ 8192 ≤ 8192
  decide +kernel

theorem first_excess_rejected {R : Type} [Field R] (proof : Proof R) : ¬ CounterAccepted (repeated 8193 proof) := by
  rw [Airbender.NativeMainBatchProofs.counter_iff]
  change ¬ ((0 : Nat) < 8193 ∧ 8193 ≤ 8192)
  decide +kernel

/-- PURE count/capacity control, NOT a source/global/caller attack witness. -/
theorem beyond_field_capacity_still_passes_count {R : Type} [Field R] (proof : Proof R) :
    CounterAccepted (repeated 257 proof) ∧ mersenne31Modulus < 257*8388607 := by
  constructor
  · rw [Airbender.NativeMainBatchProofs.counter_iff]
    change (0 : Nat) < 257 ∧ 257 ≤ 8192
    decide +kernel
  · decide +kernel

theorem largest_capacity_below_cycle_limit : 8192*8388607=68719468544 ∧ 8192*8388607<68719476736 := by decide +kernel

theorem u32_product_u64_headroom : (2^32-1)*8388607 < (2^64 : Nat) := by decide +kernel

private theorem duplicate_fold {A : Type} (item : A) (cap : Nat) :
    [item,item].foldl (fun cycles _ => cycles + cap) 0 = 2*cap := by
  rw [Airbender.NativeMainBatchProofs.fold_count]
  simp only [List.length_cons,List.length_nil,Nat.zero_add]

theorem duplicate_proofs_counted {R : Type} [Field R] (proof : Proof R) :
    ([proof,proof].foldl (fun cycles _ => cycles+8388607) 0 : Nat)=2*8388607 :=
  duplicate_fold proof 8388607

theorem actual_all_ordinary_count {R : Type} [Field R] (batch : Batch R) :
    (Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs batch.proofs)).length =
      batch.proofs.length*capacity := Airbender.NativeMainBatchProofs.ordinary_count batch

theorem complete_conditional_joint {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted embed memory ch pc gamma config batch workers inputs inverse) :
    Effects batch ∧ Airbender.NativeWorkerClockProgress.Effects workers :=
  native_counted_main_worker_progress embed memory ch pc gamma config accepted
end Airbender.Tests.NativeMainBatch
