import Airbender.Review.Circuits.ReducedMachine.TokenLedger
import Airbender.Proofs.ReducedMachine.NativeMemoryTokens
import Airbender.Proofs.ReducedMachine.NativeMainArguments

namespace Airbender.NativeTokenLedgerProofs
open NativeTokenLedger NativeMemoryTokens Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem port_product {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (w : Nat → F) (write : Bool) :
    ((portTokens w write).map (argument embed memory pc)).prod =
      if write then mainWrite embed memory pc w else mainRead embed memory pc w := by
  cases write <;> simp [portTokens,argument,List.map_map,Function.comp_def,
    NativeMemoryTokenProofs.main_product,mainRead,mainWrite]

theorem row_product {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    {w : Nat → F} {aux : Airbender.Blake2Worker.QuarticColumn → R} {next : R}
    (accepted : RowAccepted embed memory pc w aux next) (write : Bool) :
    ((rowTokens w write).map (argument embed memory pc)).prod = rowFactor embed memory pc w write := by
  cases write
  · simp [rowTokens,argument,NativeMemoryTokenProofs.argument_encoding,port_product,rowFactor]
  · rw [rowFactor,Airbender.ReducedMachine.NativeMainAuxiliaryProofs.mask_choice embed memory pc accepted]
    by_cases active : w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1
    all_goals simp [rowTokens,active,argument,NativeMemoryTokenProofs.argument_encoding,port_product]

theorem worker_product {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (w : Nat → F) (write : Bool) :
    ((workerRowTokens w write).map (argument embed memory pc)).prod = memoryKeyProduct embed memory w write := by
  simpa only [workerRowTokens,List.map_map,argument,Function.comp_def] using
    NativeMemoryTokenProofs.worker_product embed memory w write

theorem public_product {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (inputs : PublicBoundary) (write : Bool) :
    ((publicTokens inputs write).map (argument embed memory pc)).prod =
      registerProduct embed memory (if write then registerInitialKey else registerFinalKey inputs) *
        pcArgument embed pc (if write then initialPCKey else finalPCKey inputs) := by
  cases write <;> simp [publicTokens,List.map_map,Function.comp_def,argument,registerProduct,
    NativeMemoryTokenProofs.argument_encoding]

private theorem flattened_product {A R : Type} [CommMonoid R] (rows : List A)
    (tokens : A → List Token) (compress : Token → R) :
    ((rows.flatMap tokens).map compress).prod =
      (rows.map fun row => ((tokens row).map compress).prod).prod := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons,ih]

private theorem range_product {R : Type} [CommMonoid R] (n : Nat) (f : Nat → R) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ,Finset.prod_range_succ,ih]

private theorem batch_product {A B R : Type} [CommMonoid R]
    (proofs : List A) (rows : A → Nat → B) (n : Nat) (tokens : B → List Token)
    (compress : Token → R) (factor : B → R)
    (bound : ∀ proof ∈ proofs, ∀ i < n, ((tokens (rows proof i)).map compress).prod = factor (rows proof i)) :
    ((((proofs.flatMap fun proof => (List.range n).map (rows proof)).flatMap tokens).map compress).prod) =
      (proofs.map fun proof => ∏ i ∈ Finset.range n, factor (rows proof i)).prod := by
  rw [List.flatMap_assoc,flattened_product]
  congr 1
  apply List.map_congr_left
  intro proof member
  rw [List.flatMap_map,flattened_product,range_product]
  apply Finset.prod_congr rfl
  intro i present
  exact bound proof member i (Finset.mem_range.mp present)

theorem main_product {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (mains : List (MainProof R))
    (accepted : ∀ proof ∈ mains, Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof)
    (write : Bool) :
    (((mainRows mains).flatMap fun w => rowTokens w write).map (argument embed memory pc)).prod =
      mainBatchProduct embed memory pc mains write := by
  exact batch_product mains MainProof.rows _ (fun w => rowTokens w write)
    (argument embed memory pc) (fun w => rowFactor embed memory pc w write)
    (fun proof member i bound => row_product embed memory pc ((accepted proof member).rows i bound) write)

theorem workers_product {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (batch : WorkerBatch Setup R) (write : Bool) :
    (((workerRows batch).flatMap fun w => workerRowTokens w write).map (argument embed memory pc)).prod =
      workerBatchProduct embed memory batch write := by
  exact batch_product batch.outputs (fun output => output.proof.rows) _
    (fun w => workerRowTokens w write) (argument embed memory pc)
    (fun w => memoryKeyProduct embed memory w write)
    (fun output _ i _ => worker_product embed memory pc (output.proof.rows i) write)

theorem full_product {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary)
    (accepted : ∀ proof ∈ mains, Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof)
    (write : Bool) :
    ((fullTokens mains batch inputs write).map (argument embed memory pc)).prod =
      registerProduct embed memory (if write then registerInitialKey else registerFinalKey inputs) *
        pcArgument embed pc (if write then initialPCKey else finalPCKey inputs) *
        mainBatchProduct embed memory pc mains write * workerBatchProduct embed memory batch write := by
  simp only [fullTokens,List.map_append,List.prod_append,public_product,
    main_product embed memory pc mains accepted,workers_product]

theorem accepted_product_balance {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R) (pc : PCChallenges R)
    (config : WorkerConfiguration Setup) {mains : List (MainProof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed memory processor pc config mains batch inputs inverse) :
    ((fullTokens mains batch inputs true).map (argument embed memory pc)).prod =
      ((fullTokens mains batch inputs false).map (argument embed memory pc)).prod := by
  rw [full_product embed memory pc mains batch inputs accepted.mainProofs true,
    full_product embed memory pc mains batch inputs accepted.mainProofs false]
  exact Airbender.ReducedMachine.NativeMainAuxiliaryProofs.main_worker_balance embed memory processor pc config accepted

theorem row_partition (w : Nat → F) (write : Bool) :
    rowTokens w write = activeRowTokens w write ++ inactiveRowTokens w := by
  by_cases active : w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1
  all_goals cases write <;> simp [rowTokens,activeRowTokens,inactiveRowTokens,active]

/-- This is cancellation of identical uncompressed token MULTISETS, preserving
    duplicates. It is never division by possibly-zero challenge factors. -/
theorem full_partition {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) :
    (fullTokens mains batch inputs write).Perm
      (activeTokens mains batch inputs write ++ (mainRows mains).flatMap inactiveRowTokens) := by
  unfold fullTokens activeTokens
  simp_rw [row_partition]
  have partition := List.flatMap_append_perm (mainRows mains)
    (fun w => activeRowTokens w write) inactiveRowTokens
  apply Multiset.coe_eq_coe.mp
  have equality := Multiset.coe_eq_coe.mpr partition.symm
  simp only [← Multiset.coe_add] at equality ⊢
  rw [equality]
  ac_rfl

theorem matching_iff {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    LogicalMatching mains batch inputs ↔
      (activeTokens mains batch inputs true).Perm (activeTokens mains batch inputs false) := by
  unfold LogicalMatching
  have left := full_partition mains batch inputs true
  have right := full_partition mains batch inputs false
  constructor
  · intro matching
    have equality := Multiset.coe_eq_coe.mpr (left.symm.trans (matching.trans right))
    apply Multiset.coe_eq_coe.mp
    simpa only [← Multiset.coe_add,add_right_cancel_iff] using equality
  · intro matching
    exact left.trans ((matching.append_right _).trans right.symm)

theorem projected_matching {Setup R : Type} [Field R] {mains : List (MainProof R)}
    {batch : WorkerBatch Setup R} {inputs : PublicBoundary} (matching : LogicalMatching mains batch inputs) :
    ((activeTokens mains batch inputs true).filterMap memoryProjection).Perm
      ((activeTokens mains batch inputs false).filterMap memoryProjection) ∧
    ((activeTokens mains batch inputs true).filterMap stateProjection).Perm
      ((activeTokens mains batch inputs false).filterMap stateProjection) := by
  have active := (matching_iff mains batch inputs).mp matching
  exact ⟨active.filterMap _,active.filterMap _⟩

end Airbender.NativeTokenLedgerProofs
