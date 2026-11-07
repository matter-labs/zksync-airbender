import Airbender.Review.Trace.Families.ReducedMachine.FixedData
import Airbender.Proofs.Trace.ZeroValues
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryDecoder
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDecodedResult

namespace Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
open Native Arithmetic Trace Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Readonly ports refresh their actual prior reads. LW alone writes a masked
    GPR; the actual SW third port is a memory cell and cannot be x0. -/
theorem row_zero_preserving (row : Row mersenne31Modulus NativeReducedFamily)
    {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowZeroPreserving row := by
  cases row with
  | mk family w =>
    cases family
    intro port member address reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _) address
    · exact reads importedConstraintsMemoryPorts[1]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _) address
    · have destination := NativeWordMemoryPortProofs.addresses holds fields query 2
      cases mode : entry.data.family
      · have cell : (Cell.register entry.data.rd).addressCode = (Cell.register 0).addressCode := by
          simpa [wordMemoryPortCells,mode] using destination.symm.trans address
        have zero : entry.data.rd = 0 := Cell.register.inj (cell_address_injective cell)
        have write : wordMemoryWrittenWord w = (⟨0,0⟩ : Word) := by
          simpa [wordMemoryResult,mode,zero] using NativeWordMemoryResultProofs.written_result holds fields query
        have low := congrArg Word.lo write
        have high := congrArg Word.hi write
        change Nat.pair (w 43).val (w 44).val = 0
        change (w 43).val = 0 at low
        change (w 44).val = 0 at high
        rw [low,high]
        rfl
      · have cell : (Cell.ram (wordMemoryAddressWord w).toBitVec).addressCode =
            (Cell.register 0).addressCode := by
          simpa [wordMemoryPortCells,mode] using destination.symm.trans address
        have impossible := cell_address_injective cell
        cases impossible

/-- Original full public decoding supplies every native per-row x0 rule. -/
theorem decoded_zero_preserving {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup) :
    ZeroPreserving (fixedData trace) := by
  intro row member
  obtain ⟨entry,_,source,query,_⟩ := NativeWordMemoryDecoderProofs.trace_decoding image accepted decoded row member
  exact row_zero_preserving row (accepted.constraints row member) source.fields query

end Airbender.ReducedMachine.NativeWordMemoryHistoryProofs
