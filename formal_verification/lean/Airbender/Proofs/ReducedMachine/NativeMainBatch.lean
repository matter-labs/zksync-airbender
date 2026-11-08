import Airbender.Review.Circuits.ReducedMachine.MainBatch
import Airbender.Proofs.ReducedMachine.NativeWorkerClockProgress

namespace Airbender.NativeMainBatchProofs
open Airbender.NativeMainBatch
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Entire constant-capacity fold BEFORE native data/domain instantiation. -/
theorem fold_count {A : Type} (items : List A) (cap start : Nat) :
    items.foldl (fun cycles _ => cycles + cap) start = start + items.length*cap := by
  induction items generalizing start with
  | nil => simp
  | cons item items ih => simp only [List.foldl_cons,ih,List.length_cons,Nat.succ_mul]; omega

/-- Entire source processed-guard calculation over abstract finite observations. -/
theorem list_guards {A : Type} (items : List A) (cap limit : Nat) (positive : 0 < cap) :
    (0 < items.length ∧
      (∀ i < items.length, (items.take (i + 1)).foldl (fun cycles _ => cycles + cap) 0 < limit) ∧
      0 < items.foldl (fun cycles _ => cycles + cap) 0) ↔
    0 < items.length ∧ items.length*cap < limit := by
  simp only [fold_count,Nat.zero_add]
  constructor
  · rintro ⟨nonempty,processed,_⟩
    have last := processed (items.length-1) (by omega)
    have same : items.length-1 + 1=items.length := by omega
    rw [same,List.take_length] at last
    exact ⟨nonempty,last⟩
  · rintro ⟨nonempty,full⟩
    refine ⟨nonempty,?_,Nat.mul_pos nonempty positive⟩
    intro i _
    have small : (items.take (i + 1)).length ≤ items.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    exact lt_of_le_of_lt (Nat.mul_le_mul_right cap small) full

/-- Generic sampling length; no concrete2^23 evaluation or deduplication. -/
theorem sampled_length {A B : Type} (items : List A) (rows : A → Nat → B) (count : Nat) :
    (items.flatMap (fun item => (List.range count).map (rows item))).length = items.length*count := by
  induction items with
  | nil => simp
  | cons item items ih => simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_range,ih,
      List.length_cons,Nat.succ_mul]; omega

theorem geometry : capacity = 8388607 ∧ maxCycles = 68719476736 := ⟨rfl,rfl⟩

theorem count_binding {R : Type} [Field R] (batch : Batch R) : batch.proofs.length = batch.countWord.toNat := by
  simp [Batch.proofs]

theorem prefix_count {R : Type} [Field R] (batch : Batch R) (processed : Nat) :
    prefixCycles batch processed = (batch.proofs.take processed).length*capacity := by
  exact (fold_count _ capacity 0).trans (Nat.zero_add _)

theorem total_count {R : Type} [Field R] (batch : Batch R) :
    prefixCycles batch batch.countWord.toNat = batch.proofs.length*capacity := by
  rw [prefix_count,← count_binding,List.take_length]

theorem counter_iff {R : Type} [Field R] (batch : Batch R) :
    CounterAccepted batch ↔ 0 < batch.countWord.toNat ∧ batch.countWord.toNat ≤ 8192 := by
  have generic := list_guards batch.proofs capacity maxCycles (by rw [geometry.1]; decide)
  change (0 < batch.countWord.toNat ∧ (∀ i < batch.countWord.toNat, _ ) ∧ _) ↔ _
  rw [← count_binding batch]
  simp only [prefixCycles,List.take_length]
  rw [generic]
  rw [geometry.1,geometry.2]
  omega

/-- Entire integer headroom calculation BEFORE structured prefix/count data. -/
theorem natural_headroom {length word : Nat} (bounded : length ≤ word) (u32 : word < 4294967296) :
    length*8388607 < 18446744073709551616 := by omega

/-- u32 count and fixed selected capacity give u64 headroom independently of
    the counter guard. This is not arbitrary Rust arithmetic refinement. -/
theorem headroom {R : Type} [Field R] (batch : Batch R) (processed : Nat) : prefixCycles batch processed < 2^64 := by
  rw [prefix_count,geometry.1]
  have length : (batch.proofs.take processed).length ≤ batch.proofs.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  rw [count_binding] at length
  have word : batch.countWord.toNat < 2^32 := BitVec.isLt _
  change batch.countWord.toNat < 4294967296 at word
  change (List.take processed batch.proofs).length*8388607 < 18446744073709551616
  exact natural_headroom length word

theorem ordinary_count {R : Type} [Field R] (batch : Batch R) :
    (Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs batch.proofs)).length =
      batch.proofs.length*capacity := by
  rw [Airbender.NativeTokenLedger.mainRows,sampled_length]
  simp only [Airbender.NativeInitializationBatch.mainProofs,List.length_map,capacity]

theorem effects {R : Type} [Field R] (batch : Batch R) (accepted : CounterAccepted batch) : Effects batch := by
  obtain ⟨positive,bound⟩ := (counter_iff batch).mp accepted
  have total := total_count batch
  have count := count_binding batch
  have ordinary := ordinary_count batch
  have last : prefixCycles batch batch.countWord.toNat < maxCycles := by
    have selected := accepted.2.1 (batch.countWord.toNat-1) (by omega)
    simpa only [show batch.countWord.toNat-1 + 1=batch.countWord.toNat by omega] using selected
  refine ⟨count,by omega,by omega,total,last,ordinary.trans total.symm,?_,fun processed _ => headroom batch processed⟩
  rw [ordinary,geometry.1]
  omega

theorem joint {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted embed memory ch pc gamma config batch workers inputs inverse) :
    Effects batch ∧ Airbender.NativeWorkerClockProgress.Effects workers :=
  ⟨effects batch accepted.counter,Airbender.NativeWorkerClockProgressProofs.effects embed memory ch pc gamma config accepted.component⟩
end Airbender.NativeMainBatchProofs
