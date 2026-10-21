import Airbender.Review.Trace.Families.SubwordMemory.Loads
import Tests.SubwordOddX0Fixture
import Tests.SubwordDecoderOriginal

namespace Tests.SubwordOddX0
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordOddX0Row Tests.SubwordOddX0Fixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def setup : SparseDecoderSetup Operation := ⟨[some entry],1048575⟩

theorem fields : SubwordMemory.decoderFields entry.instruction = some entry.data := rfl

theorem actual_bytes : (Cell.ram 0).read before = .ok entry.bits before := by
  simp [Cell.read,_root_.Sail.ArchSem.readBytes,_root_.Sail.ArchSem.readByte,
    EStateM.run,get,getThe,MonadStateOf.get,bind,pure,EStateM.bind,EStateM.get,EStateM.pure,
    before,entry,Std.ExtHashMap.getElem_insert]

theorem original_decode :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards entry.bits) before = .ok entry.instruction before := by
  rw [show SailRV32.Functions.encdec_backwards entry.bits = .pure entry.instruction from
    Tests.SubwordDecoderOriginal.decoded_3]
  rfl

theorem constructed : SubwordMemory.sparseDecoderSetupImage before 1 20 = some setup := by
  have slot : programSlotRunWith SubwordMemory.decoderFields before 0 = some (some entry) := by
    simp only [programSlotRunWith,actual_bytes,original_decode,bind,Option.bind,pure,fields,Option.map_some]
    rfl
  change (([0] : List (BitVec 32)).mapM (programSlotRunWith SubwordMemory.decoderFields before)).bind
    (fun slots => some (SparseDecoderSetup.mk slots 1048575)) = some setup
  simp only [List.mapM_cons,List.mapM_nil,slot,bind,Option.bind,pure]
  rfl

theorem query : decoderQuery assignment = entry.query := by decide +kernel

theorem decoded : Decoded trace setup := by
  intro actual present
  have same : actual = nativeRow := by simpa [trace] using present
  subst actual
  change setup.table.Contains #[] (decoderQuery assignment)
  rw [query]
  exact Airbender.Trace.Proofs.sparse_head_member entry [] 1048575

/-- Full actual acceptance and original initialization/decoding retain odd
    discarded halfwords. This is not a successful original execution claim. -/
theorem public_loads : ∀ row ∈ trace.rows, ∃ selected ∈ setup.program,
    selected.SourceWith before SubwordMemory.decoderFields ∧ DecodedFields row.assignment selected ∧
    NativeAddress row.assignment ∧ NativeLoadEffects trace.rom row.assignment selected :=
  SubwordMemory.public_native_loads constructed public_inputs accepted decoded

theorem actual_odd_write :
    assignment 22 = 3 ∧ (assignment 22).val % 2 = 1 ∧ assignment 8 = 1 ∧
    (writtenWord assignment).toBitVec = 0 ∧ assignment 60 = 0 ∧ assignment 61 = 0 := by
  decide +kernel

end Tests.SubwordOddX0
