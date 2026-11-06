import Airbender.Proofs.Trace.Families.ReducedMachine.Results

namespace Airbender.ReducedMachine.Native
open Trace Arithmetic
set_option autoImplicit false

/-- Public decoding, initialization and native matching derive canonical complete
    RV32 candidate/write results, including discarded x0 writes. No source range
    or expected value is an input. Original Sail GPR/cell transport and execution,
    numerical PC and broader setup/physical fidelity remain separate. -/
theorem public_shift_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧ ShiftDecoded row.assignment entry ∧
      candidateWord row.assignment = Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec
          ((operandWord row.assignment).toBitVec.extractLsb' 0 5).toNat) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (sourceWord row.assignment).toBitVec
          ((operandWord row.assignment).toBitVec.extractLsb' 0 5).toNat) :=
  NativeShiftRangeProofs.image_shift_results image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
