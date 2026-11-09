import Airbender.Review.Trace.Families.ReducedMachine.ControlArithmetic

namespace Airbender.NativeControlLogic
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Original RV32 bitwise reference on exact initialized tokens. Immediate forms
    keep the second native read while selecting the original immediate. -/
def bitwiseReference (w : Nat → F) (entry : BitwiseProgramEntry) : BitVec 32 :=
  entry.data.family.result (Airbender.NativeMainDependencies.read w 0).word.toBitVec
    (if entry.data.family.useRegister then (Airbender.NativeMainDependencies.read w 1).word.toBitVec else entry.data.immediate.toBitVec)

def comparisonReference (w : Nat → F) (entry : ComparisonProgramEntry) : BitVec 32 :=
  entry.data.family.result (Airbender.NativeMainDependencies.read w 0).word.toBitVec
    (if entry.data.family.useRegister then (Airbender.NativeMainDependencies.read w 1).word.toBitVec else entry.data.immediate.toBitVec)

def BitwiseResult (w : Nat → F) (entry : BitwiseProgramEntry) : Prop :=
  (Airbender.NativeMainDependencies.write w 2).word =
    if entry.data.rd = 0 then ⟨0,0⟩ else Arithmetic.Word.ofBitVec (bitwiseReference w entry)

def ComparisonResult (w : Nat → F) (entry : ComparisonProgramEntry) : Prop :=
  (Airbender.NativeMainDependencies.write w 2).word =
    if entry.data.rd = 0 then ⟨0,0⟩ else Arithmetic.Word.ofBitVec (comparisonReference w entry)

/-- Actual decoded rd12 third-port edges, retaining every full raw token. -/
def Edges {Mode R : Type} [Field R] (projection : SailRV32.instruction → Option (DecoderData Mode))
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (path : List Token) : Prop :=
  ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ entry : ProgramEntry Mode,
    projection entry.instruction = some entry.data → row.decoderQuery = entry.query → entry.data.rd = 12 →
    (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs
  bitwise : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : BitwiseProgramEntry,
    bitwiseDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → BitwiseResult row.assignment entry
  comparison : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : ComparisonProgramEntry,
    comparisonDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query →
    ComparisonResult row.assignment entry ∧ (limbs (Airbender.NativeMainDependencies.write row.assignment 2)).2 = 0
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path
end Airbender.NativeControlLogic
