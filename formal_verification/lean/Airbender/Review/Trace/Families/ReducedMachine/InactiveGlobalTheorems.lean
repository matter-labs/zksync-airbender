import Airbender.Proofs.ReducedMachine.NativeInactiveGlobal

namespace Airbender.NativeInactiveGlobal
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Airbender.Trace

/-- Every indexed repetition of this SAME complete component is rejected by full
    source acceptance plus the OLD explicit source-identity boundary. Decoder
    logical lookups and native count limits are derived, not premises. All >=257
    copies remain covered. This is not physical activity/crypto or a native defect. -/
theorem native_repeated_inactive_source_rejected {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    (beforeMain : Airbender.ReducedMachine.NativeMainAuxiliary.MainProof R) (omega : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R)
    (completion : NativeInitializationComponent.Completion embed memory pc ch decoder gamma
      (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) beforeMain omega proof base witness setup polynomial)
    (countWord : BitVec 32) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : NativeCallerDecoder.setupImage before count 20 = some publicSetup) :
    ¬ (NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config
      (copies (packed gamma proof base witness setup polynomial omega) countWord) workers inputs inverse ∧
      NativeDelegationSupport.SourceIdentity (copies (packed gamma proof base witness setup polynomial omega) countWord).main.proofs workers) :=
  NativeInactiveGlobalProofs.reject_completion publicSetup embed memory ch pc gamma decoder config beforeMain omega
    proof base witness setup polynomial completion countWord workers inputs inverse image
end Airbender.NativeInactiveGlobal
