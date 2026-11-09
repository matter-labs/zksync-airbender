import Airbender.Proofs.ReducedMachine.NativeSparseMain

namespace Airbender.NativeSparseMain
set_option autoImplicit false
open Airbender.ReducedMachine
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Full nonconstant ordinary memory/caller component with one request position.
    The actual sparse claim and genuine normalized polynomial are derived. All
    idle rows/poles/raw accesses remain; no issued-call/global matching/worker,
    physical-verifier, original CSR/NDstream or parity claim is made. -/
theorem native_sparse_inactive_main_components {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : NativeDecoderArguments.Challenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) (nonpoles : NativeInactiveMain.Nonpoles embed memory pc ch NativeSparseMainProofs.original)
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ main : NativeMainArguments.Proof R,
      main.memory.rows = rows NativeSparseMainProofs.original position ∧ main.memory.grandClaim = 1 ∧
      Accepted embed memory pc main.memory ∧ CallerDelegationAccepted embed ch main.caller ∧
      (∀ i < callerAuxiliaryLayout.traceLength-1, NativeDecoderArguments.RowAccepted embed decoder (main.memory.rows i) (main.memory.auxiliary i)) ∧
      main.delegationClaim = (csrStageThreeArgument embed ch 1 NativeSparseMainProofs.original)⁻¹ ∧ main.delegationClaim ≠ 0 :=
  NativeSparseMainProofs.complete embed memory pc ch decoder position nonpoles omega primitive
end Airbender.NativeSparseMain
