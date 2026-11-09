import Airbender.Proofs.ReducedMachine.NativeWorkerSeed

namespace Airbender.NativeWorkerSeed
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.NativeDelegationSupport Airbender.NativeSparseMain
set_option autoImplicit false

/-- Every active worker requires an ACTUAL nonpadding initialization source row,
    derived from the complete initialized memory relation and OLD SourceIdentity.
    This is a logical seed requirement, not physical extraction or issued calls. -/
theorem native_active_worker_requires_ram_initialization {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : SourceIdentity proofs workers) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    ∃ source ∈ callerRows proofs, Airbender.NativeInitializationLedger.paddingRow source = false :=
  NativeWorkerSeedProofs.active_requires_seed embed memory ch pc gamma config accepted identity member active

/-- The SAME complete sparse main/caller component cannot extend to full source
    acceptance plus OLD SourceIdentity, for ANY surrounding observations/count/
    workers. No expected activity, initialization, count or ledger is supplied.
    Not a physical-verifier rejection, general caller activity or native defect. -/
theorem native_sparse_global_completion_rejected {Kind Setup R : Type} [Field R]
    (publicSetup : Airbender.Trace.SparseDecoderSetup Kind)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : NativeDecoderArguments.Challenges R) (gamma : R) (config : WorkerConfiguration Setup)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (nonpoles : Airbender.NativeInactiveMain.Nonpoles embed memory pc ch NativeSparseMainProofs.original)
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ main : NativeMainArguments.Proof R,
      (main.memory.rows = rows NativeSparseMainProofs.original position ∧ main.memory.grandClaim = 1 ∧
       Accepted embed memory pc main.memory ∧ CallerDelegationAccepted embed ch main.caller ∧
       (∀ i < callerAuxiliaryLayout.traceLength-1, NativeDecoderArguments.RowAccepted embed decoder (main.memory.rows i) (main.memory.auxiliary i)) ∧
       main.delegationClaim = (csrStageThreeArgument embed ch 1 NativeSparseMainProofs.original)⁻¹ ∧ main.delegationClaim ≠ 0) ∧
      ∀ surrounding : Airbender.NativeMainDecoder.Proof R, ∀ countWord : BitVec 32,
        ∀ workers : WorkerBatch Setup R, ∀ inputs : PublicBoundary, ∀ inverse : BoundaryInverses R,
        ¬ (Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config
          (Airbender.NativeInactiveGlobal.copies (withMain main surrounding) countWord) workers inputs inverse ∧
          SourceIdentity (Airbender.NativeInactiveGlobal.copies (withMain main surrounding) countWord).main.proofs workers) :=
  NativeWorkerSeedProofs.constructed_rejection publicSetup embed memory pc ch decoder gamma config position nonpoles omega primitive
end Airbender.NativeWorkerSeed
