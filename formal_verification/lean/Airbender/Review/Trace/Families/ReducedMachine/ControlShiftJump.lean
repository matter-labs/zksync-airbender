import Airbender.Review.Circuits.ReducedMachine.ShiftOperand
import Airbender.Review.Trace.Families.ReducedMachine.ControlLogic

namespace Airbender.NativeControlShiftJump
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Exact initialized source and original register/immediate shift operand. -/
def shiftReference (w : Nat → F) (entry : ShiftProgramEntry) : BitVec 32 :=
  entry.data.family.result (Airbender.NativeMainDependencies.read w 0).word.toBitVec
    (((if shiftUsesRegister entry.instruction then (Airbender.NativeMainDependencies.read w 1).word.toBitVec
      else entry.data.immediate.toBitVec).extractLsb' 0 5).toNat)

def ShiftResult (w : Nat → F) (entry : ShiftProgramEntry) : Prop :=
  (Airbender.NativeMainDependencies.write w 2).word =
    if entry.data.rd = 0 then ⟨0,0⟩ else Arithmetic.Word.ofBitVec (shiftReference w entry)

/-- JAL/JALR write the original public PC successor, independent of target/OLDREAD. -/
def JumpResult (w : Nat → F) (entry : JumpProgramEntry) : Prop :=
  (Airbender.NativeMainDependencies.write w 2).word =
    if entry.data.rd = 0 then ⟨0,0⟩ else Arithmetic.Word.ofBitVec (entry.pc + 4)

structure Effects {Setup R : Type} [Field R] (before : Reference.RiscV.Sail.State)
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs
  shifts : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : ShiftProgramEntry,
    shiftDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → ShiftResult row.assignment entry
  jumps : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : JumpProgramEntry,
    jumpDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → JumpResult row.assignment entry
  path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token) ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path
end Airbender.NativeControlShiftJump
