import Airbender.Proofs.Trace.Families.ReducedMachine.ComparisonResults

namespace Airbender.ReducedMachine.Native
open Trace Arithmetic
set_option autoImplicit false

/-- Public initialization/full original decoding and native acceptance derive
    complete RV32 comparison candidates and actual rd/x0 masked writes. No source,
    operand, PC, immediate range or result answer is supplied. Original Sail GPR/
    clause/fetched execution and native public/physical setup fidelity are separate. -/
theorem public_comparison_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ComparisonMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : comparisonDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ComparisonDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before comparisonDecoderFields ∧
      row.decoderQuery = entry.query ∧ ComparisonDecoded row.assignment entry ∧
      candidateWord row.assignment = Word.ofBitVec (entry.data.family.result
        (sourceWord row.assignment).toBitVec (operandWord row.assignment).toBitVec) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec (operandWord row.assignment).toBitVec) :=
  NativeComparisonRangeProofs.image_comparison_results image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
