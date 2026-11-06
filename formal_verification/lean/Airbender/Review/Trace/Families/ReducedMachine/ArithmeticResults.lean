import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticResults

namespace Airbender.ReducedMachine.Native
open Trace Arithmetic
set_option autoImplicit false

/-- Public initialization/full original decoding and native acceptance derive
    complete RV32 arithmetic candidates and actual rd/x0 masked writes. No source,
    operand, PC, immediate range or result answer is supplied. Original Sail GPR/
    clause/fetched execution and native public/physical setup fidelity are separate. -/
theorem public_arithmetic_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before arithmeticDecoderFields ∧
      row.decoderQuery = entry.query ∧ ArithmeticDecoded row.assignment entry ∧
      candidateWord row.assignment = Word.ofBitVec (entry.data.family.result
        (sourceWord row.assignment).toBitVec (operandWord row.assignment).toBitVec
        (initialPCWord row.assignment).toBitVec entry.data.immediate.toBitVec) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec (operandWord row.assignment).toBitVec
          (initialPCWord row.assignment).toBitVec entry.data.immediate.toBitVec) :=
  NativeArithmeticRangeProofs.image_arithmetic_results image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
