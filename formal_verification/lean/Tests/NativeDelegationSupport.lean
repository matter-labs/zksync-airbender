import Airbender.Review.Circuits.ReducedMachine.DelegationSupportTheorems

namespace Airbender.Tests.NativeDelegationSupport
open Airbender.NativeDelegationSupport Airbender.ReducedMachine.Native
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure algebra/data controls, not accepted native BODY/source witnesses. -/
private def first : Key := ⟨1991,0,0,0⟩
private def second : Key := ⟨1990,0,1,0⟩

theorem raw_keys_distinct : first ≠ second := by decide +kernel

theorem fixed_challenge_collision :
    csrArgument (⟨0,0,1,0⟩ : CSRArgumentChallenges F) first = csrArgument ⟨0,0,1,0⟩ second := by
  norm_num [csrArgument,first,second]

theorem formal_keys_distinct : keyPolynomial first ≠ keyPolynomial second :=
  fun equal => raw_keys_distinct (Airbender.NativeDelegationSupportProofs.key_injective equal)

theorem one_parameter_collision : (keyPolynomial first).eval 1 = (keyPolynomial second).eval 1 := by
  norm_num [keyPolynomial,first,second]

theorem sentinel_preserved : keyPolynomial (⟨1991,0,0,-1⟩ : Key) ≠ keyPolynomial ⟨1991,0,0,0⟩ := by
  intro equal
  have same := congrArg CSRArgumentKey.high (Airbender.NativeDelegationSupportProofs.key_injective equal)
  change (-1 : F) = 0 at same
  norm_num at same

theorem duplicates_count (w : Nat → F) :
    weightAt [w,w] callerKey (fun row => row 92) (callerKey w) = w 92+w 92 := by
  simp [weightAt]

theorem zero_weight_retained (w : Nat → F) (zero : w 92 = 0) :
    callerKey w ∈ poles [w] [] ∧ weightAt [w] callerKey (fun row => row 92) (callerKey w) = 0 := by
  simp [poles,weightAt,zero]

theorem empty_identity : FormalIdentity [] [] := rfl

/-- A non-Boolean caller contribution can support two Boolean worker positions.
    The controls deliberately do not claim these data satisfy native BODY. -/
private def caller (i : Nat) : F := if i = 92 then 2 else if i = 94 then 1991 else if i = 2 then -3 else 0
private def worker (i : Nat) : F := if i = 0 then 1 else 0

private theorem same_key : callerKey caller = workerKey worker := by
  change (⟨caller 94,caller 93,caller 2+3,caller 3⟩ : Key) = ⟨1991,worker 1,worker 740,worker 741⟩
  norm_num [caller,worker]

theorem nonboolean_caller : caller 92 = 2 ∧ caller 92 ≠ 1 := by
  change (2 : F) = 2 ∧ (2 : F) ≠ 1
  constructor
  · rfl
  · decide +kernel

theorem duplicate_worker_weights : weightAt [worker,worker] workerKey (fun w => w constraintsABI.multiplicity) (workerKey worker) = 2 := by
  change weightAt [worker,worker] workerKey (fun w => w 0) (workerKey worker) = 2
  simp [weightAt,worker]
  decide +kernel

theorem weighted_identity : FormalIdentity [caller] [worker,worker] := by
  apply congrArg (numerator (poles [caller] [worker,worker]))
  funext target
  by_cases equal : callerKey caller = target
  · have other : workerKey worker = target := same_key.symm.trans equal
    change weightAt [caller] callerKey (fun w => w 92) target = weightAt [worker,worker] workerKey (fun w => w 0) target
    simp [weightAt,equal,other,caller,worker]
    change (2 : F) = 1+1
    decide +kernel
  · have other : workerKey worker ≠ target := fun same => equal (same_key.trans same)
    simp [weightAt,equal,other]

theorem weighted_support : ∃ source ∈ [caller], source 92 ≠ 0 ∧ callerKey source = workerKey worker := by
  apply Airbender.NativeDelegationSupportProofs.support weighted_identity
  · intro w member
    have same : w = worker := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
    subst w
    exact Or.inr (by change worker 0 = 1; rfl)
  · change 2 < 2147483647
    decide +kernel
  · simp
  · change worker 0 = 1
    rfl

theorem no_caller_rejected (w : Nat → F) (active : w constraintsABI.multiplicity = 1) :
    ¬ FormalIdentity [] [w] := by
  intro identity
  have source := Airbender.NativeDelegationSupportProofs.support identity
    (by
      intro row member
      have same : row = w := by simpa using member
      subst row
      exact Or.inr active)
    (by change 1 < 2147483647; decide +kernel) (by simp) active
  obtain ⟨row,member,_,_⟩ := source
  exact List.not_mem_nil member

/-- Pure exclusions for the exact two previously checked LOCAL clock shapes.
    They are not new global accepted witnesses or native defect claims. -/
theorem wide_high_excluded :
    ¬ Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair ((0 : F),524288)) := by
  intro domain
  have high := domain.high
  change 524288 < 524288 ∨ 524288 = 2147483646 at high
  omega

theorem zero_low_high_sentinel_excluded :
    ¬ Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair ((0 : F),-1)) := by
  intro domain
  have consequence := domain.highWrap (by decide +kernel)
  have low := consequence.1
  change 524287 ≤ 0 at low
  omega

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Anchored batch.proofs workers ∧ ClockDomains workers ∧ ReadDomains batch.proofs workers :=
  native_counted_worker_support embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeDelegationSupport
