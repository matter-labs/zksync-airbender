import Airbender.Proofs.ReducedMachine.NativeControlCSR

namespace Airbender.NativeControlCSR
open Airbender.NativeWorkerSnapshot Airbender.Trace Airbender.ReducedMachine.Native
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME counted native source/public image/old logical boundaries derive
    actual CSR1991 control clears, all CSR rd12 edges on the same complete
    path, and ordinary-or-CSR1984 nonzero origins. No reset/schedule premise. -/
theorem native_counted_control_csr {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlCSRProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeControlCSR
