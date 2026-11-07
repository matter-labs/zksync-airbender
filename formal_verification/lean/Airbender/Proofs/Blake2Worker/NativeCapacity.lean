import Airbender.Review.Circuits.Blake2Worker.Capacity
import Airbender.Proofs.Blake2Worker.NativeDelegation
import Airbender.Proofs.Blake2Worker.NativeProcessing

namespace Airbender.Blake2Worker.CapacityProofs
open Verification Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem geometry : configuredWorkerType = 1991 ∧ configuredWorkerSlots = 1048575 := by decide +kernel

/-- Pure normalization of the native counter's actual repeated additions. -/
theorem slot_fold {α : Type} (outputs : List α) (slots initial : Nat) :
    outputs.foldl (fun total _ => total+slots) initial = initial+outputs.length*slots := by
  induction outputs generalizing initial with
  | nil => simp
  | cons output outputs ih =>
      simp only [List.foldl_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]
      omega

theorem capacity_counter {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) :
    statementWorkerCapacity batch = batch.outputs.length*configuredWorkerSlots := by
  simp only [statementWorkerCapacity,slot_fold,Nat.zero_add]

/-- The native32-bit stream count cannot overflow the selected u64 counter,
    independently of the later characteristic check. -/
theorem counter_fits_u64 {Setup R : Type} [Field R] (batch : WorkerBatch Setup R)
    (count : batch.outputs.length = batch.countWord.toNat) :
    statementWorkerCapacity batch < 2^64 := by
  rw [capacity_counter,count,geometry.2]
  have word := batch.countWord.isLt
  change batch.countWord.toNat < 4294967296 at word
  norm_num only [Nat.reducePow]
  omega

theorem active_bound {R : Type} [Field R] (proof : DelegationProof R) :
    workerActiveCount proof ≤ configuredWorkerSlots := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

/-- Pure finite indicator identity, kept abstract before native instantiation. -/
theorem indicator_sum (indices : Finset Nat) (values : Nat → ZMod mersenne31Modulus)
    (boolean : ∀ i ∈ indices, values i = 0 ∨ values i = 1) :
    (∑ i ∈ indices, values i) = ((indices.filter fun i => values i = 1).card : ZMod mersenne31Modulus) := by
  classical
  have indicator : ∀ i ∈ indices, values i = if values i = 1 then 1 else 0 := by
    intro i member
    rcases boolean i member with zero | one
    · rw [zero]
      simp
    · rw [one]
      simp
  calc
    _ = ∑ i ∈ indices, (if values i = 1 then 1 else 0 : ZMod mersenne31Modulus) :=
      Finset.sum_congr rfl indicator
    _ = _ := by simp

/-- Processing acceptance derives the indicators before counting them. -/
theorem multiplicity_count {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {proof : DelegationProof R} (accepted : DelegationAccepted embed memory processor proof) :
    workerMultiplicitySum proof = (workerActiveCount proof : ZMod mersenne31Modulus) := by
  apply indicator_sum
  intro i member
  exact (ProcessingProofs.effects
    (accepted.trace.rows i (Finset.mem_range.mp member)).body.conventions).multiplicityBit

theorem list_active_bound {Setup R : Type} [Field R] (outputs : List (WorkerProofOutput Setup R)) :
    (outputs.map fun output => workerActiveCount output.proof).sum ≤ outputs.length*configuredWorkerSlots := by
  induction outputs with
  | nil => simp
  | cons output outputs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      have bound := active_bound output.proof
      omega

theorem batch_bound {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) :
    batchActiveCount batch ≤ statementWorkerCapacity batch := by
  rw [capacity_counter]
  exact list_active_bound batch.outputs

theorem shared_acceptance {Setup R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch)
    (output : WorkerProofOutput Setup R) (member : output ∈ batch.outputs) :
    DelegationAccepted embed memory processor output.proof := by
  have headers := accepted.headers output member
  simpa only [headers.2.2.2.1,headers.2.2.2.2] using accepted.proofs output member

theorem sum_count_cast (counts : List Nat) :
    (List.map (fun (n : Nat) => (n : ZMod mersenne31Modulus)) counts).sum = (counts.sum : ZMod mersenne31Modulus) := by
  induction counts with
  | nil => simp
  | cons n counts ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]

theorem batch_multiplicity_count {Setup R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    batchMultiplicitySum batch = (batchActiveCount batch : ZMod mersenne31Modulus) := by
  have each : batch.outputs.map (fun output => workerMultiplicitySum output.proof) =
      batch.outputs.map (fun output => (workerActiveCount output.proof : ZMod mersenne31Modulus)) := by
    apply List.map_congr_left
    intro output member
    exact multiplicity_count embed memory processor (shared_acceptance embed memory processor config accepted output member)
  unfold batchMultiplicitySum batchActiveCount
  rw [each]
  simpa only [List.map_map,Function.comp_def] using
    sum_count_cast (batch.outputs.map fun output => workerActiveCount output.proof)

theorem configured_bounds {Setup R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    batchActiveCount batch ≤ statementWorkerCapacity batch ∧
    batchActiveCount batch < mersenne31Modulus ∧ batch.outputs.length ≤ 2048 := by
  have bound := batch_bound batch
  have cap := accepted.capacity
  have counter := capacity_counter batch
  have slots := geometry.2
  refine ⟨bound,lt_of_le_of_lt bound cap,?_⟩
  rw [counter,slots] at cap
  change batch.outputs.length*1048575 < 2147483647 at cap
  omega

/-- Exact canonical value, using the derived total bound; no characteristic
    wrap can hide additional observed active rows in this component. -/
theorem active_count_no_wrap {Setup R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    (batchActiveCount batch : ZMod mersenne31Modulus).val = batchActiveCount batch := by
  exact ZMod.val_natCast_of_lt (configured_bounds embed memory processor config accepted).2.1

theorem batch_multiplicity_no_wrap {Setup R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    (batchMultiplicitySum batch).val = batchActiveCount batch := by
  rw [batch_multiplicity_count embed memory processor config accepted]
  exact active_count_no_wrap embed memory processor config accepted

end Airbender.Blake2Worker.CapacityProofs
