import Airbender.Review.Circuits.ReducedMachine.CallerValidity
import Airbender.Review.Trace.Families.ReducedMachine.DelegationKeyAccounting

namespace Airbender.NativeCallerCount
open Airbender.NativeDelegationSupport
/-- Natural count over EVERY original occurrence. No activity/request sublist is substituted into acceptance. -/
def countAt {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K) : Nat :=
  (rows.map fun row => if key row = target ∧ weight row = 1 then 1 else 0).sum

open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

def occurrences {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (target : Key) : Nat :=
  countAt (callerRows proofs) callerKey (fun w => w 92) target

def indicator {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (target : Key) : Nat :=
  if target ∈ Airbender.NativeDelegationKeyAccounting.keys workers then 1 else 0

/-- Exact natural-count ambiguity from the SAME native source. The quotient is
    bounded, not assumed zero. This does not establish activity or a bijection. -/
structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs
  validity : Airbender.NativeCallerValidity.Effects batch.main.proofs
  perKey : ∀ target, occurrences batch.main.proofs target ≤ 68719468544 ∧
    occurrences batch.main.proofs target % mersenne31Modulus = indicator workers target ∧
      ∃ q ≤ 31, occurrences batch.main.proofs target = indicator workers target + mersenne31Modulus*q
  missing : ∀ target, target ∉ Airbender.NativeDelegationKeyAccounting.keys workers →
    occurrences batch.main.proofs target = 0 ∨ mersenne31Modulus ≤ occurrences batch.main.proofs target
  repeated : ∀ target, target ∈ Airbender.NativeDelegationKeyAccounting.keys workers →
    occurrences batch.main.proofs target = 1 ∨ mersenne31Modulus+1 ≤ occurrences batch.main.proofs target
  wrapRequiresProofs : ∀ target, occurrences batch.main.proofs target ≠ indicator workers target →
    257 ≤ batch.countWord.toNat
  workerCaller : ∀ target, target ∈ Airbender.NativeDelegationKeyAccounting.keys workers →
    ∃ caller ∈ callerRows batch.main.proofs, caller 92 = 1 ∧ callerKey caller = target
end Airbender.NativeCallerCount

