import Airbender.Review.Circuits.ReducedMachine.MemoryTokens
import Airbender.Review.Circuits.ReducedMachine.MainArguments

namespace Airbender.NativeTokenLedger
open Airbender.NativeMemoryTokens Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- The two native permutation-factor families remain distinct before challenge
    compression. This is a logical observation, not compression injectivity. -/
inductive Token where
  | memory (key : Trace.MemoryToken mersenne31Modulus)
  | state (key : PCKey)
  deriving DecidableEq

def memoryProjection : Token → Option (Trace.MemoryToken mersenne31Modulus)
  | .memory token => some token
  | .state _ => none

def stateProjection : Token → Option PCKey
  | .memory _ => none
  | .state key => some key

def argument {R : Type} [CommRing R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) : Token → R
  | .memory token => tokenArgument embed memory token
  | .state key => pcArgument embed pc key

/-- Both readonly refreshes and the third OLDREAD/unmasked write are retained. -/
def portTokens (w : Nat → F) (write : Bool) : List Token :=
  (mainTokens w write).map Token.memory ++ [Token.state (mainPCKey w write)]

/-- Every ordinary row contributes teardown/read on the read side. On the write
    side the native execute mask chooses outgoing or incoming ports AND state.
    Booleanity is derived separately from the complete accepted native body. The
    initialization/teardown pair is unmasked, including execute-zero rows. -/
def rowTokens (w : Nat → F) (write : Bool) : List Token :=
  [Token.memory (encodeKey (initializationKey w write))] ++
    portTokens w (write && decide (w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1))

/-- Only the port/state contribution is filtered. This filters no caller request,
    no initialization token, and no worker access. -/
def activeRowTokens (w : Nat → F) (write : Bool) : List Token :=
  [Token.memory (encodeKey (initializationKey w write))] ++
    if w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1 then portTokens w write else []

def inactiveRowTokens (w : Nat → F) : List Token :=
  if w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1 then [] else portTokens w false

def mainRows {R : Type} [Field R] (proofs : List (MainProof R)) : List (Nat → F) :=
  proofs.flatMap fun proof => (List.range (Airbender.ReducedMachine.Native.callerAuxiliaryLayout.traceLength-1)).map proof.rows

def workerRows {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) : List (Nat → F) :=
  batch.outputs.flatMap fun output => (List.range (constraintsABI.traceLength-1)).map output.proof.rows

def publicTokens (inputs : PublicBoundary) (write : Bool) : List Token :=
  ((List.finRange 32).map fun index => Token.memory (encodeKey
    (if write then registerInitialKey index else registerFinalKey inputs index))) ++
    [Token.state (if write then initialPCKey else finalPCKey inputs)]

def workerRowTokens (w : Nat → F) (write : Bool) : List Token :=
  (workerTokens w write).map Token.memory

/-- ALL native ordinary rows, all32 public registers including x0 timestamps,
    public PC, all initialization/teardown pairs and all43 worker accesses. No
    expected ledger, initialized read or fulfilled-request stream is supplied. -/
def fullTokens {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) : List Token :=
  publicTokens inputs write ++ (mainRows mains).flatMap (fun w => rowTokens w write) ++
    (workerRows batch).flatMap (fun w => workerRowTokens w write)

def activeTokens {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) : List Token :=
  publicTokens inputs write ++ (mainRows mains).flatMap (fun w => activeRowTokens w write) ++
    (workerRows batch).flatMap (fun w => workerRowTokens w write)

/-- Exact precompression logical acceptance over the actual full native token
    observations. As in pinned v3 Clean acceptance, cryptographic extraction is
    explicit and separate: fixed-challenge sums/products do NOT establish this
    permutation. This relation supplies no expected read/value/range/clock or
    issued/fulfilled worker stream, and asserts no physical setup/codec proof. -/
def LogicalMatching {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop :=
  (fullTokens mains batch inputs true).Perm (fullTokens mains batch inputs false)

end Airbender.NativeTokenLedger
