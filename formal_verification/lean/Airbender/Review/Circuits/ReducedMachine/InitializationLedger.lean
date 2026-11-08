import Airbender.Review.Circuits.ReducedMachine.InitializationBatch

namespace Airbender.NativeInitializationLedger
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.NativeMemoryTokens Airbender.NativeTokenLedger
abbrev F := ZMod mersenne31Modulus

/-- Test ALL six actual initialization/teardown fields, including value/time.
    Zero address alone is not the padding test. No execute filter is used. -/
def paddingRow (w : Nat → F) : Bool := initializationColumns.all fun column => decide (w column = 0)

def initializationToken (w : Nat → F) (write : Bool) := encodeKey (initializationKey w write)

/-- Canonical native RAM address coding with TWO bounded limbs. This does not
    prescribe an architectural/public RAM region, alignment or image coverage. -/
def RAM32 (token : Trace.MemoryToken mersenne31Modulus) : Prop :=
  (Nat.unpair token.address).1 = 1 ∧
    (Nat.unpair (Nat.unpair token.address).2).1 < 65536 ∧
    (Nat.unpair (Nat.unpair token.address).2).2 < 65536

def addressValue (token : Trace.MemoryToken mersenne31Modulus) : Nat :=
  (Nat.unpair (Nat.unpair token.address).2).1 + 65536 * (Nat.unpair (Nat.unpair token.address).2).2

/-- Actual native zero seed observation. Public image/domain coverage and
    chronological initialized memory are further results, not this definition. -/
def ZeroSeed (token : Trace.MemoryToken mersenne31Modulus) : Prop :=
  RAM32 token ∧ token.value = 0 ∧ token.time = (0,0)

def paddingTokens (w : Nat → F) : List Token :=
  if paddingRow w then [Token.memory (initializationToken w true)] else []

/-- Remove ONLY the identical padded initialization pair. Keep active port/state
    effects even on a row whose initialization record is padding. -/
def retainedRowTokens (w : Nat → F) (write : Bool) : List Token :=
  (if paddingRow w then [] else [Token.memory (initializationToken w write)]) ++
    if w importedConstraintsTraceColumns.execute = 1 then portTokens w write else []

/-- Actual nonpadding seed/teardown list, in supplied main-proof/ordinary-row
    order, with duplicates preserved. No expected public seed list is supplied. -/
def initializationTokens {R : Type} [Field R] (mains : List (MainProof R)) (write : Bool) : List Token :=
  (mainRows mains).flatMap fun w => if paddingRow w then [] else [Token.memory (initializationToken w write)]

/-- Public register/PC boundary, active main port/state effects and ALL worker
    accesses. Inactive caller requests are not filtered by this memory view. -/
def accessTokens {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : Airbender.Blake2Worker.Native.WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) (write : Bool) : List Token :=
  publicTokens inputs write ++
    (mainRows mains).flatMap (fun w => if w importedConstraintsTraceColumns.execute = 1 then portTokens w write else []) ++
    (workerRows batch).flatMap (fun w => workerRowTokens w write)

/-- Actual full main/worker/public observations after exact multiset cancellation
    of inactive incoming ports/state and identical padded initialization pairs.
    All43 worker ports and all32 public registers including x0 timestamps remain. -/
def retainedTokens {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : Airbender.Blake2Worker.Native.WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) (write : Bool) : List Token :=
  publicTokens inputs write ++ (mainRows mains).flatMap (fun w => retainedRowTokens w write) ++
    (workerRows batch).flatMap (fun w => workerRowTokens w write)

end Airbender.NativeInitializationLedger
