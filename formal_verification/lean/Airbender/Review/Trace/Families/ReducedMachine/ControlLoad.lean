import Airbender.Review.Trace.Families.ReducedMachine.ControlShiftJump
import Airbender.Review.Circuits.ReducedMachine.WordMemoryResult

namespace Airbender.NativeControlLoad
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Original sign-extended offset added to the exact initialized first read. -/
def addressReference (w : Nat → F) (entry : WordMemoryProgramEntry) : Arithmetic.Word :=
  Arithmetic.Word.ofBitVec ((Airbender.NativeMainDependencies.read w 0).word.toBitVec + entry.data.immediate.toBitVec)

/-- ROM comes from the native eight-word fixture and UNIMP tail; RAM uses the
    actual initialized second read. The retained ROM shadow token is separate. -/
def loadReference (w : Nat → F) (entry : WordMemoryProgramEntry) : Arithmetic.Word :=
  let address := addressReference w entry
  if address.hi < 64 then wordMemoryROMWord (address.value / 4) else (Airbender.NativeMainDependencies.read w 1).word

structure LoadResult (w : Nat → F) (entry : WordMemoryProgramEntry) : Prop where
  address : wordMemoryAddressWord w = addressReference w entry
  aligned : (addressReference w entry).value % 4 = 0
  written : (Airbender.NativeMainDependencies.write w 2).word =
    if entry.data.rd = 0 then ⟨0,0⟩ else loadReference w entry

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs
  loads : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : WordMemoryProgramEntry,
    wordMemoryDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query →
    entry.data.family = false → LoadResult row.assignment entry
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path
end Airbender.NativeControlLoad
