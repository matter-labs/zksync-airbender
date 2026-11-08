import Airbender.Review.Circuits.ReducedMachine.InitializationSeedDomain
import Airbender.Proofs.ReducedMachine.NativeInitializationLedger
import Airbender.Proofs.Arithmetic.Word
import Mathlib.Data.List.FinRange

namespace Airbender.NativeInitializationSeedDomainProofs
open Airbender.NativeInitializationSeedDomain
open Airbender.NativeInitializationLedger (F paddingRow ZeroSeed RAM32 addressValue)
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem finite_sampling {A B : Type} (items : List A) (observe : A → B) :
    ((List.finRange items.length).map fun i => observe (items[i.val]'i.isLt)) = items.map observe := by
  rw [← List.ofFn_eq_map]
  exact List.ofFn_getElem_eq_map items observe

theorem finite_rows {A : Type} (count : Nat) (observe : Nat → A) :
    ((List.finRange count).map fun i => observe i.val) = (List.range count).map observe := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp

theorem position_sampling {A B : Type} (items : List A) (count : Nat) (observe : A → Nat → B) :
    (((List.finRange items.length).product (List.finRange count)).map
      (fun index => observe (items[index.1.val]'index.1.isLt) index.2.val)) =
      items.flatMap (fun item => (List.range count).map (observe item)) := by
  simp only [List.product,List.map_flatMap,List.map_map,Function.comp_def]
  change ((List.finRange items.length).flatMap fun c =>
    (List.finRange count).map fun i => observe (items[c.val]'c.isLt) i.val) = _
  simp_rw [finite_rows]
  exact congrArg List.flatten (finite_sampling items (fun item => (List.range count).map (observe item)))

/-- Entire finite-list uniqueness argument over ABSTRACT objects/domain before
    concrete native rows. Positions have finite bounds; there is no OOB fallback. -/
theorem sampled_unique {A B K : Type} (items : List A) (count : Nat) (observe : A → Nat → B)
    (keep : B → Bool) (key : B → K)
    (unique : ∀ c d : Fin items.length, ∀ i j : Fin count,
      keep (observe (items[c.val]'c.isLt) i.val) = true →
      keep (observe (items[d.val]'d.isLt) j.val) = true →
      key (observe (items[c.val]'c.isLt) i.val) = key (observe (items[d.val]'d.isLt) j.val) → c = d ∧ i = j) :
    ((((items.flatMap fun item => (List.range count).map (observe item)).filter keep).map key)).Nodup := by
  rw [← position_sampling items count observe,List.filter_map,List.map_map]
  apply List.Nodup.map_on _ (((List.nodup_finRange items.length).product (List.nodup_finRange count)).filter _)
  intro left lm right rm same
  obtain ⟨c,i⟩ := unique left.1 right.1 left.2 right.2 (List.mem_filter.mp lm).2 (List.mem_filter.mp rm).2 same
  exact Prod.ext c i

/-- Generic canonical RAM32 token calculation; the whole RV32 address stays Nat
    before BitVec construction. No whole-word M31 cast or supplied cell equality. -/
theorem token_cell {token : Trace.MemoryToken mersenne31Modulus} (zero : ZeroSeed token) :
    token = (cell token).initialToken 0 := by
  let low := (Nat.unpair (Nat.unpair token.address).2).1
  let high := (Nat.unpair (Nat.unpair token.address).2).2
  have bounded : (⟨low,high⟩ : Arithmetic.Word).Bounded := zero.1.2
  have word : Arithmetic.Word.ofBitVec (BitVec.ofNat 32 (addressValue token)) = ⟨low,high⟩ := by
    apply Arithmetic.Word.eq_of_value (Arithmetic.Word.ofBitVec_bound _) bounded
    rw [Arithmetic.Word.ofBitVec_value]
    exact Arithmetic.Word.toBitVec_toNat bounded
  have address : (cell token).addressCode = token.address := by
    simp only [cell,Trace.Cell.addressCode,word]
    have joined := Nat.pair_unpair token.address
    rw [zero.1.1,← Nat.pair_unpair (Nat.unpair token.address).2] at joined
    exact joined
  have value : (Arithmetic.Word.ofBitVec (0 : BitVec 32)).lo = 0 ∧
      (Arithmetic.Word.ofBitVec (0 : BitVec 32)).hi = 0 := by decide +kernel
  cases token with
  | mk a t v =>
    obtain ⟨_,rfl,rfl⟩ := zero
    simpa only [Trace.Cell.initialToken,address,value.1,value.2] using
      (show (⟨a,(0,0),0⟩ : Trace.MemoryToken mersenne31Modulus) = ⟨a,(0,0),Nat.pair 0 0⟩ by rfl)

theorem same_ledger {R : Type} [Field R] (proofs : List (Proof R)) (write : Bool) :
    Airbender.NativeInitializationLedger.initializationTokens (mainProofs proofs) write =
      (tokens proofs write).map Airbender.NativeTokenLedger.Token.memory := by
  unfold Airbender.NativeInitializationLedger.initializationTokens tokens sources
  rw [List.map_map]
  generalize Airbender.NativeTokenLedger.mainRows (mainProofs proofs) = rows
  induction rows with
  | nil => rfl
  | cons w rows ih =>
    by_cases padding : paddingRow w = true
    · simp [padding,ih]
    · have noPadding : paddingRow w = false := Bool.eq_false_iff.mpr padding
      simp [noPadding,ih]

theorem seed_domains {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs := by
  have canonical : ∀ token ∈ tokens proofs true, ZeroSeed token := by
    intro token member
    obtain ⟨w,wm,rfl⟩ := List.mem_map.mp member
    have original := (List.mem_filter.mp wm).1
    obtain ⟨main,mm,row⟩ := List.mem_flatMap.mp original
    obtain ⟨proof,pm,rfl⟩ := List.mem_map.mp mm
    obtain ⟨i,ib,rfl⟩ := List.mem_map.mp row
    exact (NativeInitializationLedgerProofs.accepted_domains embed memory ch pc gamma config accepted pm i (List.mem_range.mp ib)).1
  have effects := NativeInitializationBatchProofs.initialization_effects embed memory ch pc gamma config accepted
  have length : scalar16Layout.traceLength = callerAuxiliaryLayout.traceLength := by decide +kernel
  have unique := sampled_unique proofs (scalar16Layout.traceLength-1) (fun proof i => proof.main.memory.rows i)
    (fun w => !paddingRow w) (fun w => (Airbender.NativeInitializationLedger.initializationToken w true).address) ?_
  · have addresses : ((tokens proofs true).map Trace.MemoryToken.address).Nodup := by
      simpa only [tokens,sources,Airbender.NativeTokenLedger.mainRows,mainProofs,List.flatMap_map,List.map_map,Function.comp_def,length] using unique
    have codes : (cells proofs).map Trace.Cell.addressCode = (tokens proofs true).map Trace.MemoryToken.address := by
      rw [cells,List.map_map]
      apply List.map_congr_left
      intro token member
      exact congrArg Trace.MemoryToken.address (token_cell (canonical token member)).symm
    have domain : (cells proofs).Nodup := List.Nodup.of_map Trace.Cell.addressCode (codes.symm ▸ addresses)
    refine ⟨canonical,addresses,domain,?_⟩
    rw [cells,List.map_map]
    calc
      tokens proofs true = (tokens proofs true).map id := (List.map_id _).symm
      _ = _ := List.map_congr_left (fun token member => token_cell (canonical token member))
  · intro c d i j left right same
    have notPadding {w : Nat → F} (h : (!paddingRow w) = true) : ¬ Airbender.NativeInitializationOrdering.PaddingRecord w := by
      intro padding
      have p := (NativeInitializationLedgerProofs.padding_test w).mpr padding
      simp [p] at h
    obtain ⟨chunk,row⟩ := effects.unique c.val d.val i.val j.val c.isLt d.isLt i.isLt j.isLt
      (notPadding left) (notPadding right) same
    exact ⟨Fin.ext chunk,Fin.ext row⟩

theorem matching {Setup R : Type} [Field R] (proofs : List (Proof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching (mainProofs proofs) batch inputs ↔
      ((tokens proofs true).map Airbender.NativeTokenLedger.Token.memory ++
        Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs true).Perm
      ((tokens proofs false).map Airbender.NativeTokenLedger.Token.memory ++
        Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs false) := by
  rw [NativeInitializationLedgerProofs.seed_access_matching,same_ledger,same_ledger]

end Airbender.NativeInitializationSeedDomainProofs
