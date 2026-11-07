import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryResults
import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryValues

namespace Tests.NativeReducedWordMemoryValues
open Airbender Arithmetic Trace ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All actual native memory and register reads, including the unchecked low
    first source, must inherit canonical ranges from public initialization. -/
theorem oversized_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells)
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 35).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_word_memory_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at actual
  exact Nat.not_le_of_gt actual.1 large

/-- The actual second read remains bounded even when the ROM candidate ignores
    its value. It cannot be removed from native matching. -/
theorem oversized_second_read_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells)
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 37).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_word_memory_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[1] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.read_word] at actual
  exact Nat.not_le_of_gt actual.1 large

theorem oversized_destination_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells)
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (large : limbBase ≤ (row.assignment 43).val) : ¬ Accepted (fixedData trace) := by
  intro accepted
  have actual := (public_word_memory_value_bounds image inputs accepted decoded).2.1 row present
    importedConstraintsMemoryPorts[2] (by cases row; rename_i family w; cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  rw [Trace.Proofs.write_word] at actual
  exact Nat.not_le_of_gt actual.1 large

theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells)
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (token : MemoryToken mersenne31Modulus) (present : token ∈ (fixedData trace).terminalMemory)
    (large : limbBase ≤ token.word.hi) : ¬ Accepted (fixedData trace) := by
  intro accepted
  exact Nat.not_le_of_gt ((public_word_memory_value_bounds image inputs accepted decoded).2.2 token present).2 large

private def loadEntry : WordMemoryProgramEntry :=
  ⟨0,0x0100a183,.LOAD (16,.Regidx 1,.Regidx 3,false,4),⟨false,1,0,3,⟨16,0⟩,1025,2⟩⟩
private def zeroLoadEntry : WordMemoryProgramEntry :=
  ⟨0,0x0100a003,.LOAD (16,.Regidx 1,.Regidx 0,false,4),⟨false,1,0,0,⟨16,0⟩,1025,2⟩⟩
private def storeEntry : WordMemoryProgramEntry :=
  ⟨0,0x0020a823,.STORE (16,.Regidx 2,.Regidx 1,4),⟨true,1,2,0,⟨16,0⟩,16386,2⟩⟩
private theorem load_fields : wordMemoryDecoderFields loadEntry.instruction = some loadEntry.data := rfl
private theorem zero_fields : wordMemoryDecoderFields zeroLoadEntry.instruction = some zeroLoadEntry.data := rfl
private theorem store_fields : wordMemoryDecoderFields storeEntry.instruction = some storeEntry.data := rfl

theorem corrupt_load_shadow_cell_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = loadEntry.query)
    (bad : importedConstraintsMemoryPorts[1].address.code w ≠
      (Cell.ram (wordMemoryAddressWord w).toBitVec).addressCode) : False := by
  exact bad (by simpa [wordMemoryPortCells,loadEntry] using NativeWordMemoryPortProofs.addresses holds load_fields query 1)

theorem corrupt_store_memory_cell_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = storeEntry.query)
    (bad : importedConstraintsMemoryPorts[2].address.code w ≠
      (Cell.ram (wordMemoryAddressWord w).toBitVec).addressCode) : False := by
  exact bad (by simpa [wordMemoryPortCells,storeEntry] using NativeWordMemoryPortProofs.addresses holds store_fields query 2)

/-- The freshly derived RAM-only store address excludes every ROM-prefix cell.
    This does not assume a code frame or original memory value. -/
theorem store_cannot_write_rom_prefix {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = storeEntry.query) (address : BitVec 32) (inside : address.toNat < 4194304) :
    importedConstraintsMemoryPorts[2].address.code w ≠ (Cell.ram address).addressCode :=
  NativeWordMemoryPortProofs.store_excludes_rom_cell holds store_fields query rfl address inside

/-- Actual SW writes the full second word even though original decoded rd=0. -/
theorem store_dummy_rd_preserves_write {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = storeEntry.query) : wordMemoryWrittenWord w = wordMemorySecondWord w := by
  simpa [wordMemoryResult,storeEntry] using NativeWordMemoryResultProofs.written_result holds store_fields query

theorem load_x0_write_zero {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w = zeroLoadEntry.query) : wordMemoryWrittenWord w = ⟨0,0⟩ := by
  simpa [wordMemoryResult,zeroLoadEntry] using NativeWordMemoryResultProofs.written_result holds zero_fields query

/-- Distinct actual shadow inputs select the same fixed ROM word at address0.
    This is a numerical reference check, not full native acceptance or Sail memory. -/
private def sample (hi readLo readHi : Nat) (i : Nat) : ZMod mersenne31Modulus :=
  if i = 62 then hi else if i = 37 then readLo else if i = 38 then readHi else 0

theorem independent_rom_ram_references :
    wordMemoryLoadWord (sample 0 123 456) = ⟨32947,16⟩ ∧
    wordMemoryLoadWord (sample 0 65535 65535) = ⟨32947,16⟩ ∧
    wordMemoryLoadWord (sample 64 123 456) = ⟨123,456⟩ ∧
    wordMemoryLoadWord (sample 63 123 456) = ⟨4211,49152⟩ := by decide +kernel

/-- Native memory profiles retain full RV32 PC wrap after public incoming-PC
    binding; no per-row increment/carry/PC result is supplied. -/
theorem original_pc_wrap {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (query : decoderQuery w =
      ({ loadEntry with pc := 0xfffffffc } : WordMemoryProgramEntry).query) : (finalPCWord w).toBitVec = 0 := by
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec (0xfffffffc : BitVec 32) at canonical
  have aligned : (initialPCWord w).lo%4 = 0 := by rw [canonical]; decide +kernel
  have result := (NativeWordMemoryPCProofs.selected_pc_successor (entry := { loadEntry with pc := 0xfffffffc }) holds load_fields query aligned).2
  rw [canonical,Word.ofBitVec_roundtrip] at result
  simpa using result

end Tests.NativeReducedWordMemoryValues
