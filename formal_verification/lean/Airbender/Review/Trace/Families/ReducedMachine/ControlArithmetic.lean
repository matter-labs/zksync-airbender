import Airbender.Review.Trace.Families.ReducedMachine.ControlCSR
import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult

namespace Airbender.NativeControlArithmetic
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- RV32 arithmetic reference on actual initialized read tokens and original
    public PC/immediate. Register and immediate forms keep both native reads. -/
def reference (w : Nat → F) (entry : ArithmeticProgramEntry) : BitVec 32 :=
  entry.data.family.result (Airbender.NativeMainDependencies.read w 0).word.toBitVec
    (if entry.data.family.useRegister then (Airbender.NativeMainDependencies.read w 1).word.toBitVec
      else entry.data.immediate.toBitVec) entry.pc entry.data.immediate.toBitVec

def Result (w : Nat → F) (entry : ArithmeticProgramEntry) : Prop :=
  (Airbender.NativeMainDependencies.write w 2).word =
    if entry.data.rd = 0 then ⟨0,0⟩ else Arithmetic.Word.ofBitVec (reference w entry)

def Edges {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (path : List Token) : Prop :=
  ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ entry : ArithmeticProgramEntry,
    arithmeticDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → entry.data.rd = 12 →
    (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs
  arithmetic : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : ArithmeticProgramEntry,
    arithmeticDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → Result row.assignment entry
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    (∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : CSRProgramEntry,
      csrDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → entry.data.rd = 12 →
      (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail) ∧
    Edges batch.main.proofs path
end Airbender.NativeControlArithmetic
