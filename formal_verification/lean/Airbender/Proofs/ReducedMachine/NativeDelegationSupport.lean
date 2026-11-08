import Airbender.Review.Circuits.ReducedMachine.DelegationSupport
import Airbender.Proofs.ReducedMachine.NativeActiveWorkerClocks
import Airbender.Proofs.ReducedMachine.NativeCallerClockDomain
import Airbender.Proofs.ReducedMachine.NativeCSRArgument
import Airbender.Proofs.ReducedMachine.NativeMainBatch

namespace Airbender.NativeDelegationSupportProofs
open Airbender.NativeDelegationSupport
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Entire algebraic support argument BEFORE native data/domain instantiation. -/
private theorem residue {K D : Type} [DecidableEq K] [CommRing D]
    (support : Finset K) (pole : K → D)
    (weights : K → D) {target : K} (member : target ∈ support) :
    Polynomial.eval (-pole target)
      (∑ key ∈ support, Polynomial.C (weights key) *
        ∏ other ∈ support.erase key, (Polynomial.X + Polynomial.C (pole other))) =
      weights target * ∏ other ∈ support.erase target, (pole other-pole target) := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single target]
  · simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod,
      Polynomial.eval_add,Polynomial.eval_X,neg_add_eq_sub]
  · intro key present different
    have inside : target ∈ support.erase key := Finset.mem_erase.mpr ⟨Ne.symm different,member⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod,
      Polynomial.eval_add,Polynomial.eval_X]
    have zero : (∏ other ∈ support.erase key, (-pole target+pole other)) = 0 := by
      apply Finset.prod_eq_zero inside
      simp
    rw [zero,mul_zero]
  · exact fun absent => (absent member).elim

private theorem coefficients_of_identity {K D : Type} [DecidableEq K] [CommRing D] [IsDomain D]
    (support : Finset K) (pole : K → D) (injective : Function.Injective pole)
    (left right : K → D)
    (identity : (∑ key ∈ support, Polynomial.C (left key) *
        ∏ other ∈ support.erase key, (Polynomial.X + Polynomial.C (pole other))) =
      ∑ key ∈ support, Polynomial.C (right key) *
        ∏ other ∈ support.erase key, (Polynomial.X + Polynomial.C (pole other)))
    {target : K} (member : target ∈ support) : left target = right target := by
  have evaluated := congrArg (Polynomial.eval (-pole target)) identity
  rw [residue support pole left member,residue support pole right member] at evaluated
  have nonzero : (∏ other ∈ support.erase target, (pole other-pole target)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro other present
    exact sub_ne_zero.mpr (fun equal => (Finset.mem_erase.mp present).1 (injective equal))
  exact mul_right_cancel₀ nonzero evaluated

/-- Boolean finite rows and a length bound, not caller-count assumptions. -/
private theorem indicator {A : Type} (rows : List A) (weight : A → F)
    (boolean : ∀ row ∈ rows, weight row = 0 ∨ weight row = 1) :
    (rows.map weight).sum = ((rows.filter fun row => weight row = 1).length : F) := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have bit := boolean row (by simp)
    have tail := ih (fun item present => boolean item (by simp [present]))
    rcases bit with zero | one
    · simp [zero,tail]
    · simp [one,tail,Nat.cast_add,add_comm]

private theorem positive_weight {A K : Type} [DecidableEq K]
    (rows : List A) (key : A → K) (weight : A → F)
    (boolean : ∀ row ∈ rows, weight row = 0 ∨ weight row = 1)
    (bound : rows.length < mersenne31Modulus)
    {row : A} (member : row ∈ rows) (active : weight row = 1) :
    weightAt rows key weight (key row) ≠ 0 := by
  let selected := rows.filter fun item => key item = key row
  have selectedMember : row ∈ selected := List.mem_filter.mpr ⟨member,by simp⟩
  have present : row ∈ selected.filter (fun item => weight item = 1) :=
    List.mem_filter.mpr ⟨selectedMember,by simpa using active⟩
  have positive : 0 < (selected.filter fun item => weight item = 1).length :=
    List.length_pos_iff.mpr (by intro empty; rw [empty] at present; exact List.not_mem_nil present)
  have small : (selected.filter fun item => weight item = 1).length < mersenne31Modulus :=
    lt_of_le_of_lt ((List.length_filter_le _ _).trans (List.length_filter_le _ _)) bound
  have equality := indicator selected weight (fun item source => boolean item (List.mem_filter.mp source).1)
  change (selected.map weight).sum ≠ 0
  rw [equality]
  intro zero
  have value := congrArg ZMod.val zero
  rw [ZMod.val_natCast_of_lt small] at value
  have zeroValue : (0 : F).val = 0 := rfl
  rw [zeroValue] at value
  omega

private theorem nonzero_source {A K : Type} [DecidableEq K]
    (rows : List A) (key : A → K) (weight : A → F) (target : K)
    (nonzero : weightAt rows key weight target ≠ 0) :
    ∃ row ∈ rows, weight row ≠ 0 ∧ key row = target := by
  by_contra absent
  apply nonzero
  apply List.sum_eq_zero
  intro value present
  obtain ⟨row,source,rfl⟩ := List.mem_map.mp present
  obtain ⟨member,equal⟩ := List.mem_filter.mp source
  by_contra nonzero
  exact absent ⟨row,member,nonzero,by simpa using equal⟩

theorem key_injective : Function.Injective keyPolynomial := by
  intro left right same
  have kind := congrArg (fun p : Polynomial F => p.coeff 0) same
  have abi := congrArg (fun p : Polynomial F => p.coeff 1) same
  have low := congrArg (fun p : Polynomial F => p.coeff 2) same
  have high := congrArg (fun p : Polynomial F => p.coeff 3) same
  simp [keyPolynomial] at kind abi low high
  cases left
  cases right
  simp_all

/-- Exact specialization of BOTH previously reviewed native denominator forms. -/
theorem caller_denominator (w : Nat → F) (gamma parameter : F) :
    gamma + (keyPolynomial (callerKey w)).eval parameter =
      csrStageThreeArgument (RingHom.id F) ⟨gamma,parameter,parameter^2,parameter^3⟩ 1 w := by
  rw [Airbender.ReducedMachine.NativeCSRArgumentProofs.unit_scaling]
  simp only [keyPolynomial,callerKey,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,csrStageTwoArgument,csrArgument,RingHom.id_apply]
  ring

theorem worker_denominator (w : Nat → F) (gamma parameter : F) :
    gamma + (keyPolynomial (workerKey w)).eval parameter =
      processorArgument (RingHom.id F) ⟨gamma,parameter,parameter^2,parameter^3⟩ w 1 := by
  simp only [keyPolynomial,workerKey,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,processorArgument,RingHom.id_apply]
  ring

theorem coefficient_balance {callers workers : List (Nat → F)}
    (identity : FormalIdentity callers workers) {target : Key} (member : target ∈ poles callers workers) :
    weightAt callers callerKey (fun w => w 92) target =
      weightAt workers workerKey (fun w => w constraintsABI.multiplicity) target := by
  apply Polynomial.C_injective
  exact coefficients_of_identity (poles callers workers) keyPolynomial key_injective
    _ _ identity member

/-- No Booleanity, cardinality bound or execution assumption on caller rows. -/
theorem support {callers workers : List (Nat → F)}
    (identity : FormalIdentity callers workers)
    (boolean : ∀ w ∈ workers, w constraintsABI.multiplicity = 0 ∨ w constraintsABI.multiplicity = 1)
    (bound : workers.length < mersenne31Modulus)
    {worker : Nat → F} (member : worker ∈ workers) (active : worker constraintsABI.multiplicity = 1) :
    ∃ caller ∈ callers, caller 92 ≠ 0 ∧ callerKey caller = workerKey worker := by
  have keyMember : workerKey worker ∈ poles callers workers :=
    Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨worker,member,rfl⟩))
  have balanced := coefficient_balance identity keyMember
  have nonzero := positive_weight workers workerKey (fun w => w constraintsABI.multiplicity) boolean bound member active
  apply nonzero_source callers callerKey (fun w => w 92) (workerKey worker)
  rwa [balanced]

private theorem sampled_length {A B : Type} (items : List A) (rows : A → Nat → B) (count : Nat) :
    (items.flatMap fun item => (List.range count).map (rows item)).length = items.length*count := by
  induction items with
  | nil => simp
  | cons item items ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem worker_length {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) :
    (Airbender.NativeTokenLedger.workerRows batch).length = statementWorkerCapacity batch := by
  rw [Airbender.Blake2Worker.CapacityProofs.capacity_counter]
  exact sampled_length batch.outputs (fun output => output.proof.rows) (constraintsABI.traceLength-1)

theorem anchored {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : SourceIdentity proofs batch) : Anchored proofs batch := by
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted
  have boolean : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
      w constraintsABI.multiplicity = 0 ∨ w constraintsABI.multiplicity = 1 := by
    intro w member
    exact (Airbender.Blake2Worker.ProcessingProofs.effects (processing w member).conventions).multiplicityBit
  have bound : (Airbender.NativeTokenLedger.workerRows batch).length < mersenne31Modulus := by
    rw [worker_length]
    exact accepted.arguments.globalMemory.workers.capacity
  exact fun worker member active => support identity boolean bound member active

theorem clock_domain {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : SourceIdentity proofs batch) :
    ∀ worker ∈ Airbender.NativeTokenLedger.workerRows batch, worker constraintsABI.multiplicity = 1 →
      Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair (Airbender.NativeActiveWorkerClocks.workerClock worker)) := by
  have anchoring := anchored embed memory ch pc gamma config accepted identity
  have callers := Airbender.NativeCallerClockDomainProofs.all_rows embed memory ch pc gamma config accepted
  intro worker member active
  obtain ⟨caller,source,_,same⟩ := anchoring worker member active
  have low := congrArg CSRArgumentKey.low same
  have high := congrArg CSRArgumentKey.high same
  change caller 2+3 = worker constraintsABI.writeTime[0] at low
  change caller 3 = worker constraintsABI.writeTime[1] at high
  simp only [Nat.cast_ofNat] at low
  have domain := (callers caller source).domain
  change Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair (caller 2+3,caller 3)) at domain
  rw [low,high] at domain
  exact domain
private theorem bounded_domain (clock : Trace.Timestamp) (bounded : clock.Bounded) :
    Airbender.NativeCallerClockDomain.Domain clock := by
  change clock.lo < 524288 ∧ clock.hi < 524288 at bounded
  refine ⟨Or.inl (by have lower := bounded.1; omega),Or.inl bounded.2,fun _ => bounded.2,?_⟩
  intro sentinel
  have upper := bounded.2
  change clock.hi = 2147483646 at sentinel
  omega

/-- Existing actual read-source extraction plus newly conditional worker support;
    no old-read value/address/clock or matching-worker result is assumed. -/
theorem read_domains {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : SourceIdentity proofs batch) : ReadDomains proofs batch := by
  have reads := Airbender.NativeActiveWorkerClockProofs.read_clocks embed memory ch pc gamma config accepted
  have workers := clock_domain embed memory ch pc gamma config accepted identity
  intro token member
  rcases reads.clocks token member with bounded | writer
  · exact bounded_domain _ bounded
  · obtain ⟨worker,source,_,active,_,same⟩ := writer
    rw [same]
    exact workers worker source active

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Anchored batch.proofs workers ∧ ClockDomains workers ∧ ReadDomains batch.proofs workers :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    anchored embed memory ch pc gamma config accepted.component identity,
    clock_domain embed memory ch pc gamma config accepted.component identity,
    read_domains embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeDelegationSupportProofs
