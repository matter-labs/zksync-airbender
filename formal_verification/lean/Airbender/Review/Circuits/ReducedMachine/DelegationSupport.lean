import Airbender.Review.Circuits.ReducedMachine.CallerClockDomain
import Airbender.Review.Circuits.ReducedMachine.ActiveWorkerClocks
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Airbender.NativeDelegationSupport
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Key := CSRArgumentKey F

/-- The actual unit-normalized native caller tuple, on ALL ordinary rows.
    Execute-zero requests and arbitrary raw multiplicities are retained. -/
def callerKey (w : Nat → F) : Key := ⟨w 94,w 93,w 2+3,w 3⟩
def workerKey (w : Nat → F) : Key :=
  ⟨1991,w constraintsABI.offsetHigh,w constraintsABI.writeTime[0],w constraintsABI.writeTime[1]⟩

/-- Formal specialization alphaABI=Y, alphaLow=Y², alphaHigh=Y³. Its four
    coefficients retain the raw tuple without any range/Boolean assumption. -/
noncomputable def keyPolynomial (key : Key) : Polynomial F :=
  Polynomial.C key.kind + Polynomial.C key.abi * Polynomial.X +
    Polynomial.C key.low * Polynomial.X^2 + Polynomial.C key.high * Polynomial.X^3

/-- Every position contributes its raw field weight, including duplicates.
    The finite pole support below never deduplicates this weighted row list. -/
def weightAt {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K) : F :=
  ((rows.filter fun row => key row = target).map weight).sum

def poles (callers workers : List (Nat → F)) : Finset Key :=
  (callers.map callerKey).toFinset ∪ (workers.map workerKey).toFinset

/-- Cleared simple-pole numerator over a common DISTINCT pole support. Actual
    multiplicities are aggregated over every original position, not discarded.
    The outer variable is gamma; its coefficients are polynomials in Y. -/
noncomputable def numerator (support : Finset Key) (weight : Key → F) : Polynomial (Polynomial F) :=
  ∑ key ∈ support, Polynomial.C (Polynomial.C (weight key)) *
    ∏ other ∈ support.erase key, (Polynomial.X + Polynomial.C (keyPolynomial other))

/-- NEW explicit formal/cryptographic extraction boundary on the SAME actual
    native observations. It is a polynomial identity, not a supplied matching
    ledger, caller activity, clock bound or fulfilled stream. Fixed-challenge
    auxiliary equations/sums/capacity do NOT establish it. This is neither a
    physical verifier theorem nor a transcript/soundness probability bound. -/
def FormalIdentity (callers workers : List (Nat → F)) : Prop :=
  numerator (poles callers workers) (weightAt callers callerKey fun w => w 92) =
    numerator (poles callers workers) (weightAt workers workerKey fun w => w constraintsABI.multiplicity)

def callerRows {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) :=
  Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs proofs)

/-- Source-coupled boundary, with no expected list or stream equality premise. -/
def SourceIdentity {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) : Prop :=
  FormalIdentity (callerRows proofs) (Airbender.NativeTokenLedger.workerRows batch)

/-- An active worker has a nonzero caller at the exact raw four-field key.
    This does NOT assert caller execution, uniqueness, lossless matching,
    canonical19bit clocks, initialized reads or worker Sail effects. -/
def Anchored {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) : Prop :=
  ∀ worker ∈ Airbender.NativeTokenLedger.workerRows batch,
    worker constraintsABI.multiplicity = 1 →
      ∃ caller ∈ callerRows proofs, caller 92 ≠ 0 ∧ callerKey caller = workerKey worker
/-- The previously derived caller FIELD domain, including its sentinel
    alternatives. This is deliberately weaker than canonical19bit bounds. -/
def ClockDomains {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) : Prop :=
  ∀ worker ∈ Airbender.NativeTokenLedger.workerRows batch,
    worker constraintsABI.multiplicity = 1 →
      Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair (Airbender.NativeActiveWorkerClocks.workerClock worker))
/-- Actual old-read token clocks on the same full memory ledger, including all
    worker OLDREADs/readonly refreshes. This is not initialized seed reachability. -/
def ReadDomains {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) : Prop :=
  ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false,
    Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair token.time)
end Airbender.NativeDelegationSupport
