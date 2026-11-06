import Airbender.Review.Trace.Families.ReducedMachine.Sources
import Airbender.Review.Trace.Families.ReducedMachine.Values
import Airbender.Review.Trace.Families.ReducedMachine.Decoder

namespace Tests.NativeReducedRanges
open Airbender Trace ReducedMachine Native NativeShiftNaturalProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem sll_last_amount : assembledLow .left 65535 65535 31 = 0 ∧
    assembledHigh .left 65535 65535 31 = 32768 := by decide +kernel

theorem logical_last_amount : assembledLow .right 65535 65535 31 = 1 ∧
    assembledHigh .right 65535 65535 31 = 0 := by decide +kernel

theorem arithmetic_boundaries (i : Fin 4) :
    assembledLow .arithmetic 65535 32768 (#v[0,16,17,31][i]) = (#v[65535,32768,49152,65535][i]) ∧
    assembledHigh .arithmetic 65535 32768 (#v[0,16,17,31][i]) = (#v[32768,65535,65535,65535][i]) := by
  fin_cases i <;> decide +kernel

theorem positive_arithmetic_no_fill : assembledLow .arithmetic 65535 32767 17 = 16383 ∧
    assembledHigh .arithmetic 65535 32767 17 = 0 := by decide +kernel

private theorem source_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    (source1 row.assignment)[0].val < 65536 ∧ (source1 row.assignment)[1].val < 65536 := by
  have bounds := (public_shift_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by
      cases row with
      | mk family w => cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at bounds
  exact bounds

/-- Reject the formerly unchecked low read using derived initialized ranges, not a range premise. -/
theorem oversized_low_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (bad : 65536 ≤ (source1 row.assignment)[0].val) : False := by
  have bound := (source_bounds image inputs accepted decoded row present).1
  omega

theorem oversized_write_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (port : MemoryPort) (member : port ∈ row.ports)
    (bad : 65536 ≤ (writeToken row.columns row.assignment port).word.lo ∨
      65536 ≤ (writeToken row.columns row.assignment port).word.hi) : False := by
  have bound := (public_shift_value_bounds image inputs accepted decoded).2.1 row present port member
  change _ < 65536 ∧ _ < 65536 at bound
  omega

theorem fixed_setup_exact (trace : Data mersenne31Modulus NativeReducedFamily) :
    (fixedData trace).rom = (NativeFixed.table (p := mersenne31Modulus)) ∧
      (fixedData trace).rows = trace.rows := ⟨rfl,rfl⟩

theorem both_native_key_boundaries :
    (ShiftMode.left.lookupKey 65535 31).val = 2097151 ∧
      (ShiftMode.right.lookupKey 65535 31).val = 4194303 := by decide +kernel

/-- Discarding the write never discards initialized source participation. -/
theorem discarded_write_ranges {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (discarded : rdZeroFlag row.assignment = 1) :
    rdWrite row.assignment = #v[0,0] ∧
      (source1 row.assignment)[0].val < 65536 ∧ (source1 row.assignment)[1].val < 65536 := by
  have bounds := source_bounds image inputs accepted decoded row present
  obtain ⟨entry,_,_,_,fields⟩ := public_shift_decoding image accepted decoded row present
  obtain ⟨useRegister,mask⟩ := fields.mask
  have native := accepted.constraints row present
  have write : rdWrite row.assignment =
      (entry.data.family.assemble (shiftLowParts row.assignment) (shiftHighParts row.assignment)
        (shiftSignFill row.assignment)).map (fun value => (1 - rdZeroFlag row.assignment) * value) := by
    cases row with
    | mk family w => cases family; exact NativeShiftWriteProofs.write native _ useRegister mask
  have zeros (v : Vector (ZMod mersenne31Modulus) 2) :
      v.map (fun _ => (0 : ZMod mersenne31Modulus)) = #v[0,0] := by
    ext lane bound
    interval_cases lane <;> simp
  rw [discarded] at write
  simp only [sub_self,zero_mul] at write
  exact ⟨write.trans (zeros _),bounds⟩

end Tests.NativeReducedRanges
