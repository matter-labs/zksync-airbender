import Slop.Sail.PhysicalMemory

namespace Tests.SailPhysicalMemory
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def empty : State := { (default : State) with mem := Std.ExtHashMap.emptyWithCapacity }

private def byteState : State := { empty with mem := empty.mem.insert 4294967295 0x80 }
private def halfState : State :=
  { empty with mem := (empty.mem.insert 4294967294 0xff).insert 4294967295 0x80 }

set_option backward.isDefEq.respectTransparency false in
/-- Native byte/halfword transfers work at the top of RV32 memory, without
    reading or writing neighboring bytes. -/
theorem upper_byte_roundtrip :
    Sail.run (do
      let _ ← SailRV32.Functions.write_ram .Write_plain (.Store .Data)
        (.Physaddr 0xffffffff) 1 0x80 ()
      SailRV32.Functions.read_ram .Read_plain (.Load .Data)
        (.Physaddr 0xffffffff) 1 false) empty = .ok (0x80, ()) byteState := by
  have write : Sail.run (writeMemory (size := 1) 0xffffffff 0x80) empty = .ok () byteState := by rfl
  have address : ((0xffffffff : BitVec 32).setWidth 34) = (0xffffffff : BitVec 34) := by decide
  have native := write_ram_sized 0xffffffff (Or.inl rfl) 0x80 write
  rw [address] at native
  rw [Sail.run_bind_of_ok _ _ _ _ _ native]
  have read := read_ram_sized (Or.inl rfl) (address := 0xffffffff)
    (show (readBytes (ue := SailRV32.exception) 1 4294967295).run byteState = .ok 0x80 byteState by
      simp [readBytes, readByte, byteState, empty, EStateM.run, get, getThe, MonadStateOf.get,
        bind, pure, EStateM.bind, EStateM.get, EStateM.pure])
  rw [address] at read
  exact read

set_option backward.isDefEq.respectTransparency false in
theorem upper_halfword_roundtrip :
    Sail.run (do
      let _ ← SailRV32.Functions.write_ram .Write_plain (.Store .Data)
        (.Physaddr 0xfffffffe) 2 0x80ff ()
      SailRV32.Functions.read_ram .Read_plain (.Load .Data)
        (.Physaddr 0xfffffffe) 2 false) empty = .ok (0x80ff, ()) halfState := by
  have write : Sail.run (writeMemory (size := 2) 0xfffffffe 0x80ff) empty = .ok () halfState := by rfl
  have address : ((0xfffffffe : BitVec 32).setWidth 34) = (0xfffffffe : BitVec 34) := by decide
  have native := write_ram_sized 0xfffffffe (Or.inr (Or.inl rfl)) 0x80ff write
  rw [address] at native
  rw [Sail.run_bind_of_ok _ _ _ _ _ native]
  have read := read_ram_sized (Or.inr (Or.inl rfl)) (address := 0xfffffffe)
    (show (readBytes (ue := SailRV32.exception) 2 4294967294).run halfState = .ok 0x80ff halfState by
      simp [readBytes, readByte, halfState, empty, Std.ExtHashMap.getElem_insert, EStateM.run, get, getThe, MonadStateOf.get,
        bind, pure, EStateM.bind, EStateM.get, EStateM.pure])
  rw [address] at read
  exact read

set_option backward.isDefEq.respectTransparency false in
/-- The original Sail RAM path writes and reads the last RV32 word. -/
theorem upper_word_roundtrip :
    Sail.run (do
      let _ ← SailRV32.Functions.write_ram .Write_plain (.Store .Data)
        (.Physaddr 0xfffffffc) 4 0xabcdef12 ()
      SailRV32.Functions.read_ram .Read_plain (.Load .Data)
        (.Physaddr 0xfffffffc) 4 false) empty =
      .ok (0xabcdef12, ()) (wordWriteState empty 4294967292 0xabcdef12) := by
  have address : ((0xfffffffc : BitVec 32).setWidth 34) = (0xfffffffc : BitVec 34) := by decide
  have write := write_ram_word empty 0xfffffffc 0xabcdef12
  rw [address] at write
  rw [Sail.run_bind_of_ok _ _ _ _ _ write]
  have read := read_ram_word (address := 0xfffffffc) (written_word_read empty 4294967292 0xabcdef12)
  rw [address] at read
  exact read

theorem little_endian_bytes :
    (wordWriteState empty 4194304 0xabcdef12).mem[4194304]? = some 0x12 ∧
    (wordWriteState empty 4194304 0xabcdef12).mem[4194305]? = some 0xef ∧
    (wordWriteState empty 4194304 0xabcdef12).mem[4194306]? = some 0xcd ∧
    (wordWriteState empty 4194304 0xabcdef12).mem[4194307]? = some 0xab := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert written_word_byte empty 4194304 0xabcdef12 ⟨0, by decide⟩ using 2 <;> decide
  · convert written_word_byte empty 4194304 0xabcdef12 ⟨1, by decide⟩ using 2 <;> decide
  · convert written_word_byte empty 4194304 0xabcdef12 ⟨2, by decide⟩ using 2 <;> decide
  · convert written_word_byte empty 4194304 0xabcdef12 ⟨3, by decide⟩ using 2 <;> decide

private def incomplete : State :=
  { empty with mem := empty.mem.insert 4194304 0x12 |>.insert 4194305 0xef |>.insert 4194306 0xcd }

/-- Missing bytes fail in the pinned interpreter, rather than being supplied by
    the circuit witness or silently filled with zero. -/
theorem missing_fourth_byte :
    Sail.run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr 4194304) 4 false) incomplete =
        .error (.OutOfMemoryRange 4194307) incomplete := by
  apply read_ram_word_error (address := 4194304)
  simp [readBytes, readByte, incomplete, empty,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

theorem missing_halfword_byte :
    Sail.run (SailRV32.Functions.read_ram .Read_plain (.Load .Data)
      (.Physaddr 4194306) 2 false) incomplete =
        .error (.OutOfMemoryRange 4194307) incomplete := by
  apply read_ram_sized_error (address := 4194306)
  simp [readBytes, readByte, incomplete, empty,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

end Tests.SailPhysicalMemory
