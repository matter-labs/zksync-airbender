import Airbender.Review.Circuits.ReducedMachine.InitializationPublicImage
import Airbender.Review.Helpers.Memory.History

namespace Airbender.NativeMemoryHistory
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.NativeInitializationSeedBoundary (initialTokens terminalTokens)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- An explicitly empty selected worker batch, with its actual count zero.
    Full existing native acceptance is checked ON this constructed batch. -/
def emptyWorkers (Setup R : Type) [Field R] : WorkerBatch Setup R := ⟨0,[]⟩

/-- Actual execute1 main rows from ALL ordinary rows, actual runtime table,
    source public PC endpoints and complete actual GPR/RAM seed/teardown lists.
    No opcode/request filter, expected read or placeholder memory is supplied. -/
def mainTrace {R : Type} [Field R] (proofs : List (Proof R)) (inputs : PublicBoundary) :
    Trace.Data mersenne31Modulus Trace.NativeReducedFamily :=
  ⟨Airbender.NativeMainStateHistory.rows (mainProofs proofs),Airbender.ReducedMachine.NativeRuntimePool.table,
    Airbender.NativeMainStateHistory.state initialPCKey,Airbender.NativeMainStateHistory.state (finalPCKey inputs),
    initialTokens proofs,terminalTokens proofs inputs⟩

def mainWrites {R : Type} [Field R] (proofs : List (Proof R)) :=
  (Airbender.NativeMainStateHistory.rows (mainProofs proofs)).flatMap Trace.Row.writes

def workerWrites {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) :=
  (Airbender.NativeTokenLedger.workerRows batch).flatMap fun w => Airbender.NativeMemoryTokens.workerTokens w true

/-- Exact source alternatives for ALL actual main/worker reads. A worker source
    is an actual raw write token, not an expected fulfillment or initialized value. -/
structure ReadEffects {Setup R : Type} [Field R] (proofs : List (Proof R)) (batch : WorkerBatch Setup R) : Prop where
  sources : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false,
    token ∈ initialTokens proofs ∨ token ∈ mainWrites proofs ∨ token ∈ workerWrites batch
  clocks : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false,
    (Trace.timeOfPair token.time).Bounded ∨ token ∈ workerWrites batch

/-- Complete actual main memory history for the explicitly empty worker batch.
    These are derived consequences, not a supplied Trace.Accepted or desired
    read/range/history premise. Nonempty workers and Sail instruction execution
    (including CSR/MOP), alignment/platform and physical extraction stay separate. -/
structure MainEffects {R : Type} [Field R] (proofs : List (Proof R)) (inputs : PublicBoundary) : Prop where
  accepted : Trace.Accepted (mainTrace proofs inputs)
  boundary : Trace.ClockBoundary (mainTrace proofs inputs)
  domain : ((initialTokens proofs).map Trace.MemoryToken.address).Nodup
  oldClocks : ∀ row ∈ (mainTrace proofs inputs).rows, ∀ port ∈ row.ports,
    (Trace.timeOfPair (Trace.readToken row.assignment port).time).Bounded
  reads : ∀ row ∈ (mainTrace proofs inputs).rows, ∀ port ∈ row.ports, Trace.LatestRead (mainTrace proofs inputs) row port
  addresses : ∀ row ∈ (mainTrace proofs inputs).rows, ∀ port ∈ row.ports,
    port.address.code row.assignment ∈ (initialTokens proofs).map Trace.MemoryToken.address
  paths : ∀ source ∈ initialTokens proofs, ∃ path, Trace.MemoryPath (mainTrace proofs inputs) source path
  history : ∃ history, Trace.MemoryHistory (mainTrace proofs inputs) history
  publicImage : ∀ before, Airbender.NativeInitializationPublicImage.Effects proofs before

end Airbender.NativeMemoryHistory
