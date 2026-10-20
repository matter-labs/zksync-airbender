import Airbender.Proofs.ShiftBinop.Selectors
import Airbender.Proofs.Trace.StatefulDecoderSetup

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original Sail constructors determine the six-bit native mask and raw funct3. -/
theorem decoder_field_bounds {instruction : SailRV32.instruction}
    {data : DecoderData Operation} (fields : decoderFields instruction = some data) :
    data.immediate.Bounded ∧ ∃ immediate : Bool,
      data.mask = data.family.mask + (if immediate then 32 else 0) ∧
      data.funct3 = data.family.funct3 := by
  unfold decoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [instructionFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       constructor
       · first | exact Word.ofBitVec_bound _ | simp [Word.Bounded, limbBase]
       · first | exact ⟨false, rfl, rfl⟩ | exact ⟨true, rfl, rfl⟩)

/-- Native mask equations exclude every unsupported slot and the sentinel tail. -/
theorem padding_excluded {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    decoderQuery w ≠ Vector.replicate 10 (-1) := by
  intro same
  have mask := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) same
  change w 12 = -1 at mask
  have small := packed_mask_bound holds
  have minusOne : (-1 : ZMod mersenne31Modulus).val = 2147483646 := by decide +kernel
  rw [mask, minusOne] at small
  omega

/-- Actual public construction supplies original byte reads and original decoding. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry, present, same⟩ := sparse_member member (padding_excluded holds)
  exact ⟨entry, present, (run_sparse_setup_sources image present).1, same⟩

end Airbender.ShiftBinop.Proofs
