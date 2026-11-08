import Airbender.Review.Circuits.ReducedMachine.InitializationLedger
import Airbender.Proofs.ReducedMachine.NativeInitializationBatch
import Airbender.Proofs.ReducedMachine.NativeTokenLedger

namespace Airbender.NativeInitializationLedgerProofs
open Airbender.NativeInitializationLedger
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
open Airbender.NativeMemoryTokens
open Airbender.NativeTokenLedger (Token activeRowTokens portTokens activeTokens publicTokens mainRows workerRows workerRowTokens LogicalMatching)
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem padding_test (w : Nat → F) : paddingRow w = true ↔ Airbender.NativeInitializationOrdering.PaddingRecord w := by
  simp [paddingRow,Airbender.NativeInitializationOrdering.PaddingRecord]

theorem padding_key {w : Nat → F} (padding : Airbender.NativeInitializationOrdering.PaddingRecord w) (write : Bool) :
    initializationKey w write = ⟨⟨0,0,0⟩,#v[0,0],#v[0,0]⟩ := by
  obtain ⟨addr,value,time,columns⟩ := Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry
  have zero : ∀ column ∈ [126,127,128,129,130,131], w column = 0 := by simpa only [Airbender.NativeInitializationOrdering.PaddingRecord,columns] using padding
  cases write <;> simp [initializationKey,addr,value,time,zero]

theorem padding_token {w : Nat → F} (padding : Airbender.NativeInitializationOrdering.PaddingRecord w) :
    initializationToken w false = initializationToken w true := by
  simp only [initializationToken,padding_key padding]

theorem seed_fields (w : Nat → F) : (initializationToken w true).value = 0 ∧ (initializationToken w true).time = (0,0) ∧
    (initializationToken w true).address = (initializationToken w false).address := by
  simp [initializationToken,initializationKey,encodeKey,Nat.pair]

/-- Entire field-key/Nat calculation before any native row-domain instantiation. -/
theorem row_domain {w : Nat → F}
    (bounds : (Airbender.NativeInitializationOrdering.address w)[0].val < 65536 ∧
      (Airbender.NativeInitializationOrdering.address w)[1].val < 65536) :
    ZeroSeed (initializationToken w true) ∧ RAM32 (initializationToken w false) ∧
      addressValue (initializationToken w true) = Airbender.NativeInitializationSorted.addressValue w ∧
      addressValue (initializationToken w true) < 4294967296 := by
  have one : (1 : F).val = 1 := by decide +kernel
  have domain : ∀ write, RAM32 (initializationToken w write) := by
    intro write
    simpa [RAM32,initializationToken,initializationKey,encodeKey,encodeAddress,
      Airbender.NativeInitializationOrdering.address,one] using bounds
  have packed : addressValue (initializationToken w true) = Airbender.NativeInitializationSorted.addressValue w := by
    simp [addressValue,initializationToken,initializationKey,encodeKey,encodeAddress,
      Airbender.NativeInitializationSorted.addressValue,Airbender.NativeInitializationOrdering.address]
  have wordBound : Airbender.NativeInitializationSorted.addressValue w < 4294967296 := by
    unfold Airbender.NativeInitializationSorted.addressValue
    omega
  exact ⟨⟨domain true,(seed_fields w).1,(seed_fields w).2.1⟩,domain false,packed,by rw [packed]; exact wordBound⟩

theorem row_partition (w : Nat → F) (write : Bool) :
    (activeRowTokens w write).Perm (retainedRowTokens w write ++ paddingTokens w) := by
  by_cases padding : paddingRow w = true
  · have same := padding_token ((padding_test w).mp padding)
    unfold initializationToken at same
    cases write <;> simp only [activeRowTokens,retainedRowTokens,paddingTokens,padding,ite_true,List.nil_append,initializationToken]
    · rw [same]; exact List.perm_append_comm
    · exact List.perm_append_comm
  · have noPadding : paddingRow w = false := Bool.eq_false_iff.mpr padding
    simp [activeRowTokens,retainedRowTokens,paddingTokens,noPadding,initializationToken]

/-- Generic duplicate-preserving list partition BEFORE concrete native domains. -/
theorem split_rows {A B : Type} (rows : List A) (full keep common : A → List B)
    (partition : ∀ row ∈ rows, (full row).Perm (keep row ++ common row)) :
    (rows.flatMap full).Perm (rows.flatMap keep ++ rows.flatMap common) :=
  (List.Perm.flatMap_left rows partition).trans (List.flatMap_append_perm rows keep common).symm

theorem active_partition {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) :
    (activeTokens mains batch inputs write).Perm
      (retainedTokens mains batch inputs write ++ (mainRows mains).flatMap paddingTokens) := by
  have partition := split_rows (mainRows mains) (fun w => activeRowTokens w write)
    (fun w => retainedRowTokens w write) paddingTokens (fun w _ => row_partition w write)
  apply Multiset.coe_eq_coe.mp
  have equality := Multiset.coe_eq_coe.mpr partition
  simp only [activeTokens,retainedTokens,← Multiset.coe_add] at equality ⊢
  rw [equality]
  ac_rfl

private theorem ledger_split {A B : Type} (rows : List A) (before after : List B) (seeds ports : A → List B) :
    (before ++ rows.flatMap (fun row => seeds row ++ ports row) ++ after).Perm
      (rows.flatMap seeds ++ (before ++ rows.flatMap ports ++ after)) := by
  apply Multiset.coe_eq_coe.mp
  have equality := Multiset.coe_eq_coe.mpr (List.flatMap_append_perm rows seeds ports).symm
  simp only [← Multiset.coe_add] at equality ⊢
  rw [equality]
  ac_rfl

theorem retained_partition {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) :
    (retainedTokens mains batch inputs write).Perm
      (initializationTokens mains write ++ accessTokens mains batch inputs write) :=
  ledger_split (mainRows mains) (publicTokens inputs write)
    ((workerRows batch).flatMap fun w => workerRowTokens w write)
    (fun w => if paddingRow w then [] else [Token.memory (initializationToken w write)])
    (fun w => if w importedConstraintsTraceColumns.execute = 1 then portTokens w write else [])

/-- Logical multiset cancellation in BOTH directions. No challenge compression,
    division, inverse/nonzero factor, dropped duplicate or worker filter. -/
theorem matching_iff {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    LogicalMatching mains batch inputs ↔
      (retainedTokens mains batch inputs true).Perm (retainedTokens mains batch inputs false) := by
  rw [NativeTokenLedgerProofs.matching_iff]
  have left := active_partition mains batch inputs true
  have right := active_partition mains batch inputs false
  constructor
  · intro matching
    have equality := Multiset.coe_eq_coe.mpr (left.symm.trans (matching.trans right))
    apply Multiset.coe_eq_coe.mp
    simpa only [← Multiset.coe_add,add_right_cancel_iff] using equality
  · intro matching
    exact left.trans ((matching.append_right _).trans right.symm)

theorem seed_access_matching {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    LogicalMatching mains batch inputs ↔
      (initializationTokens mains true ++ accessTokens mains batch inputs true).Perm
        (initializationTokens mains false ++ accessTokens mains batch inputs false) := by
  rw [matching_iff]
  have left := retained_partition mains batch inputs true
  have right := retained_partition mains batch inputs false
  exact ⟨fun matching => left.symm.trans (matching.trans right),fun matching => left.trans (matching.trans right.symm)⟩

theorem accepted_domains {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    {proof : Airbender.NativeInitializationBatch.Proof R} (member : proof ∈ proofs)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    ZeroSeed (initializationToken (proof.main.memory.rows i) true) ∧
      RAM32 (initializationToken (proof.main.memory.rows i) false) ∧
      addressValue (initializationToken (proof.main.memory.rows i) true) =
        Airbender.NativeInitializationSorted.addressValue (proof.main.memory.rows i) ∧
      addressValue (initializationToken (proof.main.memory.rows i) true) < 4294967296 :=
  row_domain ((NativeInitializationBatchProofs.initialization_effects embed memory ch pc gamma config accepted).bounds proof member i ordinary)

end Airbender.NativeInitializationLedgerProofs
