import Airbender.Proofs.Trace.Families.JumpBranchSlt.History
import Airbender.Proofs.Trace.Families.JumpBranchSlt.Decoder
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.JumpBranchSlt.Writes

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Verification
open Airbender.Trace.Proofs

/-- Readonly refreshes preserve their read; the final masked write is locally
    bounded by the native link ranges and conditional-control table. -/
theorem row_write_rule (row : Row mersenne31Modulus JumpBranchSltFamily)
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints ()))
    (mask : (row.assignment 12).val ∈ [1,2,4,8,16])
    (flag : row.assignment 8 = 0 ∨ row.assignment 8 = 1) : RowWriteBoundsFromReads row := by
  cases row with
  | mk family w =>
    cases family
    intro port member reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · rw [write_word]
      change (Word.mk (w 38).val (w 39).val).Bounded
      exact written_limb_bounds native mask flag

theorem decoded_write_rules {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) : WriteBoundsFromReads trace := by
  intro row member
  have metadata := decoded_mask_flag image accepted decoded row member
  exact row_write_rule row (accepted.constraints row member) metadata.1 metadata.2

theorem image_value_bounds {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have clocks := image_clock_boundary (by decide) inputs
  have seeds := image_bounds inputs.image
  have rules := decoded_write_rules image accepted decoded
  exact ⟨read_bounds_of_rules (by decide) accepted clocks seeds rules,
    write_bounds_of_rules (by decide) accepted clocks seeds rules,
    terminal_bounds_of_rules (by decide) accepted clocks seeds rules⟩

end Airbender.JumpBranchSlt.Proofs
