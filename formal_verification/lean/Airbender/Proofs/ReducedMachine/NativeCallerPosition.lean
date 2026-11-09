import Airbender.Review.Trace.Families.ReducedMachine.CallerPosition
import Airbender.Proofs.ReducedMachine.NativeCallerCount

namespace Airbender.NativeCallerPositionProofs
open Airbender.NativeDelegationSupport Airbender.NativeCallerCount Airbender.NativeCallerPosition
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem member_positive {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K)
    {a : A} (member : a ∈ rows) (same : key a = target) (one : weight a = 1) :
    0 < countAt rows key weight target := by
  induction rows with
  | nil => simp at member
  | cons first tail ih =>
    have equation : countAt (first::tail) key weight target =
      (if key first = target ∧ weight first = 1 then 1 else 0) + countAt tail key weight target := rfl
    rw [equation]
    rcases List.mem_cons.mp member with equal | rest
    · subst first
      simp only [same,one,and_self,if_true]
      omega
    · have positive := ih rest
      split_ifs <;> omega

/-- One natural occurrence identifies one UNIQUE original index, even for
    repeated equal values/functions. No deduplicated membership proxy. -/
theorem one_position {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K)
    (one : countAt rows key weight target = 1) :
    ∃! i : Fin rows.length, key rows[i.val] = target ∧ weight rows[i.val] = 1 := by
  induction rows with
  | nil => simp [countAt] at one
  | cons first tail ih =>
    by_cases head : key first = target ∧ weight first = 1
    · have zero : countAt tail key weight target = 0 := by
        have eqn : 1 + countAt tail key weight target = 1 := by simpa [countAt,head] using one
        omega
      refine ⟨0,by simpa using head,?_⟩
      intro i qualifies
      refine Fin.cases (fun _ => rfl) (fun j hj => ?_) i qualifies
      have yes : key tail[j.val] = target ∧ weight tail[j.val] = 1 := by simpa using hj
      have positive := member_positive tail key weight target (List.getElem_mem j.isLt) yes.1 yes.2
      omega
    · have rest : countAt tail key weight target = 1 := by simpa [countAt,head] using one
      obtain ⟨j,hj,unique⟩ := ih rest
      refine ⟨j.succ,by simpa using hj,?_⟩
      intro i qualifies
      refine Fin.cases (fun h => False.elim (head (by simpa using h))) (fun k hk => ?_) i qualifies
      exact congrArg Fin.succ (unique k (by simpa using hk))

theorem unique_count {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F)
    (unique : ((rows.filter fun a => weight a = 1).map key).Nodup) (target : K) :
    countAt rows key weight target = if target ∈ (rows.filter fun a => weight a = 1).map key then 1 else 0 := by
  induction rows with
  | nil => simp [countAt]
  | cons first tail ih =>
    have consCount : countAt (first::tail) key weight target =
      (if key first = target ∧ weight first = 1 then 1 else 0) + countAt tail key weight target := rfl
    rw [consCount]
    by_cases one : weight first = 1
    · have selected : ((first::tail).filter fun a => weight a = 1).map key =
        key first :: (tail.filter fun a => weight a = 1).map key := by simp [one]
      rw [selected] at unique ⊢
      have parts := List.nodup_cons.mp unique
      have result := ih parts.2
      by_cases same : key first = target
      · have absent : target ∉ (tail.filter fun a => weight a = 1).map key := by simpa [same] using parts.1
        simp [one,same,absent] at result ⊢
        exact result
      · have reverse : target ≠ key first := Ne.symm same
        simp only [List.mem_cons,reverse,false_or]
        simpa [one,same] using result
    · have selected : ((first::tail).filter fun a => weight a = 1).map key =
        (tail.filter fun a => weight a = 1).map key := by simp [one]
      rw [selected] at unique ⊢
      simpa [one] using ih unique

theorem matching {A B K : Type} [DecidableEq K] (callers : List A) (workers : List B)
    (ck : A → K) (wk : B → K) (cw : A → F) (ww : B → F)
    (counts : ∀ target, countAt callers ck cw target = if target ∈ (workers.filter fun w => ww w = 1).map wk then 1 else 0)
    (unique : ((workers.filter fun w => ww w = 1).map wk).Nodup) :
    IndexMatching callers workers ck wk cw ww := by
  constructor
  · intro i active
    have positive := member_positive callers ck cw (ck callers[i.val]) (List.getElem_mem i.isLt) rfl active
    have member : ck callers[i.val] ∈ (workers.filter fun w => ww w = 1).map wk := by
      by_contra absent
      have zero := counts (ck callers[i.val])
      rw [if_neg absent] at zero
      omega
    have one : countAt workers wk ww (ck callers[i.val]) = 1 := by
      rw [unique_count workers wk ww unique,if_pos member]
    obtain ⟨j,qualifies,only⟩ := one_position workers wk ww (ck callers[i.val]) one
    refine ⟨j,⟨qualifies.2,qualifies.1.symm⟩,?_⟩
    intro k hk
    exact only k ⟨hk.2.symm,hk.1⟩
  · intro j active
    have member : wk workers[j.val] ∈ (workers.filter fun w => ww w = 1).map wk := by
      exact List.mem_map.mpr ⟨workers[j.val],List.mem_filter.mpr ⟨List.getElem_mem j.isLt,by simpa using active⟩,rfl⟩
    have one : countAt callers ck cw (wk workers[j.val]) = 1 := by rw [counts,if_pos member]
    obtain ⟨i,qualifies,only⟩ := one_position callers ck cw (wk workers[j.val]) one
    refine ⟨i,⟨qualifies.2,qualifies.1⟩,?_⟩
    intro k hk
    exact only k ⟨hk.2,hk.1⟩

open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

theorem from_prior {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeCallerCount.Effects batch workers inputs) :
    Airbender.NativeCallerPosition.Effects batch workers inputs := by
  refine ⟨prior,?_⟩
  by_cases small : batch.countWord.toNat ≤ 256
  · left
    apply matching (callerRows batch.main.proofs) (Airbender.NativeTokenLedger.workerRows workers)
      callerKey workerKey (fun w => w 92) (fun w => w constraintsABI.multiplicity)
    · intro target
      have same : occurrences batch.main.proofs target = indicator workers target := by
        by_contra different
        have large := prior.wrapRequiresProofs target different
        omega
      exact same
    · exact prior.prior.keysUnique
  · right
    omega

theorem counted {Setup R : Type} [Field R]
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
    Airbender.NativeCallerPosition.Effects batch workers inputs :=
  from_prior (Airbender.NativeCallerCountProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity)
end Airbender.NativeCallerPositionProofs
