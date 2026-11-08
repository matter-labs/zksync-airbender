import Airbender.Review.Circuits.ReducedMachine.DecodedMain
import Airbender.Review.Circuits.ReducedMachine.MainDependencies

namespace Airbender.NativeMixedWordBounds
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Initialized two-u16-limb bounds on the SAME accepted counted source.
    Actual seeds and all active main/worker writes remain exact raw tokens.
    All ordinary worker43 ports, including inactive zero-mask rows, are covered.
    Public scope is the existing ordinary7-or-CSR projection, excluding MOP.
    This is no clock recoding, online replay, worker hash result or Sail frame. -/
structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeMainDependencies.Effects batch.main.proofs workers inputs
  capacity : Airbender.NativeMainBatch.Effects batch.main
  available : ∀ token ∈ Airbender.NativeLatestReads.available batch.main.proofs workers, token.word.Bounded
  steps : ∀ read write, Airbender.NativeMixedMemoryOrder.Step batch.main.proofs workers read write →
    read.word.Bounded ∧ write.word.Bounded
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, ∀ slot : Fin 43, ∀ flag : Bool,
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot flag)).word.Bounded
  terminal : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.terminalTokens batch.main.proofs inputs, token.word.Bounded
end Airbender.NativeMixedWordBounds
