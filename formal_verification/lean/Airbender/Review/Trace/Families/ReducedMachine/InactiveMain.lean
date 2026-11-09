import Airbender.Review.Circuits.ReducedMachine.DecoderArguments

namespace Airbender.NativeInactiveMain
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Challenge-point nonpoles used to construct the unmasked memory/state chain.
    Initialization and decoder poles remain permitted. These are fixture-domain
    conditions, not a new source acceptance or caller activity assumption. -/
def Nonpoles {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F) : Prop :=
  (∀ slot : Fin 3, memoryKeyArgument embed memory (mainMemoryKey w slot false) ≠ 0) ∧
  pcArgument embed pc (mainPCKey w false) ≠ 0 ∧ csrStageThreeArgument embed ch 1 w ≠ 0

/-- SAME complete ordinary MAIN domain and SAME auxiliary observation: full
    memory/state/masking/initialization/grand chain with first/last boundaries,
    individual caller relation and decoder access. Caller/decoder/scalar sum
    polynomials, setup/table families, global statement and logical matching are
    deliberately separate obligations, not asserted by this observation. -/
def Realizes {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (w : Nat → F) (proof : MainProof R) : Prop :=
  proof.rows = (fun _ => w) ∧ proof.grandClaim = 1 ∧ Accepted embed memory pc proof ∧
  (∀ i < callerAuxiliaryLayout.traceLength-1,
    callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (proof.rows i))
      (embed (csrRequest (proof.rows i)).multiplicity) (proof.auxiliary i callerAuxiliaryLayout.request) = 0) ∧
  (∀ i < decoderAuxiliaryLayout.traceLength-1,
    Airbender.ReducedMachine.NativeDecoderArguments.RowAccepted embed decoder (proof.rows i) (proof.auxiliary i))

/-- Existential full-domain component fixture, not native global acceptance. -/
def Fixture (w : Nat → F) : Prop :=
  w importedConstraintsTraceColumns.execute = 0 ∧ csrRequest w = ⟨1,1991,some 0,3⟩ ∧
  ∀ {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R),
    Nonpoles embed memory pc ch w → ∃ proof, Realizes embed memory pc ch decoder w proof
end Airbender.NativeInactiveMain
