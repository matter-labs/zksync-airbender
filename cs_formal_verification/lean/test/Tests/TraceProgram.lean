import Slop.Sail.ResetState
import Slop.Trace.Program
import Slop.BabyBear
import Tests.SailDecoder
import Slop.Trace.CodeHistory

namespace Tests.TraceProgram
open Airbender Trace Arithmetic
open Sail.ArchSem
set_option warningAsError true

private noncomputable def before : Reference.RiscV.Sail.State :=
  { Airbender.Reference.RiscV.Sail.resetMachine with
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0xb3 : BitVec 8)
      |>.insert 1 0x81 |>.insert 2 0x20 |>.insert 3 0
      |>.insert 4 0x03 |>.insert 5 0xa1 |>.insert 6 0x40 |>.insert 7 0 }

theorem airbender_before  : Airbender.Reference.RiscV.Sail.Configured before := by
  configured_fixture [before, Airbender.Reference.RiscV.Sail.wordWriteState]


private def addEntry : ProgramEntry :=
  ⟨0, 0x002081b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .ADD),
    ⟨.addSub, 1, 2, 3, ⟨0, 0⟩, 1, 0⟩⟩

private def loadEntry : ProgramEntry :=
  ⟨4, 0x0040a103, .LOAD (4, .Regidx 1, .Regidx 2, false, 4),
    ⟨.wordMemory, 1, 0, 2, ⟨4, 0⟩, 0, 0⟩⟩

private def program : List ProgramEntry := [addEntry, loadEntry]

-- Actual byte reads followed by actual Sail decoding build both family tables.
set_option maxRecDepth 32768 in
theorem extracted : programImage before [0, 4] = some program := by
  have addBytes : (Cell.ram 0).read before = .ok 0x002081b3 before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have loadBytes : (Cell.ram 4).read before = .ok 0x0040a103 before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, addBytes, loadBytes,
    bind, Option.bind]
  rfl

theorem missing_bytes : programImage before [8] = none := by
  have absent : (Cell.ram 8).read before =
      .error (_root_.Sail.Error.OutOfMemoryRange 8) before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, EStateM.bind, EStateM.get, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, before]
  simp only [List.mapM_cons, programEntryWith, absent, bind, Option.bind]

private def addRow : Row babyBearModulus := ⟨.addSub, fun
  | 5 => 1 | 6 => 2 | 7 => 3 | 10 => 1 | _ => 0⟩

theorem native_query : addRow.decoderQuery = addEntry.query := by
  decide

theorem fetched : addRow.Fetched before := by
  have source := Proofs.program_sources extracted addEntry (by simp [program])
  exact ⟨addEntry, source, rfl, native_query, rfl, by decide⟩

-- A valid local arithmetic selector changed to zero cannot use this program entry.
theorem wrong_selector_rejected :
    ¬ (decoderTable program .addSub).Contains #[]
      (#v[0, 0, 1, 2, 3, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 9) := by
  intro member
  obtain ⟨entry, present, selected, equal⟩ := Proofs.decoder_member member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · have mask := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) equal
    norm_num [ProgramEntry.query, addEntry] at mask
  · cases selected

theorem discarded_load_retains_instruction :
    decoderFields (.LOAD (4, .Regidx 1, .Regidx 0, false, 4)) =
      some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ := by rfl

theorem negative_immediate :
    decoderFields (.ITYPE (0xfff, .Regidx 1, .Regidx 2, .ADDI)) =
      some ⟨.addSub, 1, 0, 2, ⟨65535, 65535⟩, 1, 0⟩ := by rfl

/-- Decoding is on the Airbender configuration, independent of the state's CSRs. -/
theorem decoder_on_reset : Airbender.Reference.RiscV.Sail.decodeOnReset addEntry.bits = some addEntry.instruction := by
  decode_on_reset

/-- A native RAM store preserves the fetched/decoded public ROM instruction. -/
theorem fetched_after_ram_store :
    addEntry.Source (Reference.RiscV.Sail.wordWriteState before 4194304 0xabcdef12) := by
  have source := Proofs.program_sources extracted addEntry (by simp [program])
  refine ⟨?_, source.decoded, source.fields⟩
  exact Reference.RiscV.Sail.written_word_disjoint 4194304 0xabcdef12 (by decide) source.bytes

end Tests.TraceProgram
