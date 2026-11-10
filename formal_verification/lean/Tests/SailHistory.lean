import Airbender.Proofs.Trace.SailHistory

namespace Tests.SailHistory
open Airbender Arithmetic Trace Reference Reference.RiscV.Sail
set_option warningAsError true

private def cells : List Cell := [.register 1, .register 2, .ram 4194304]
private def valueCode (value : BitVec 32) : Nat :=
  Nat.pair (Word.ofBitVec value).lo (Word.ofBitVec value).hi
private theorem value_code (value : BitVec 32) : memoryWord (valueCode value) = value := by
  simp only [memoryWord, valueCode, Nat.unpair_pair]
  change (Word.ofBitVec value).toBitVec = value
  exact Word.ofBitVec_roundtrip value
private def initial : List (MemoryToken babyBearModulus) :=
  [(.register 1 : Cell).initialToken 9, (.register 2 : Cell).initialToken 5,
    (.ram 4194304 : Cell).initialToken 0x12345678]
private def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 (9 : BitVec 32)
      |>.insert .x2 (5 : BitVec 32)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 4194304 (0x78 : BitVec 8)
      |>.insert 4194305 0x56 |>.insert 4194306 0x34 |>.insert 4194307 0x12 }

private def seed : TimestampSortedMemoryAccessList := ⟨
  initial.reverse.map (fun token => (token.address, token.address, 0, token.value)), by
    change List.Pairwise (fun (a b : MemoryAccess) => b.1 < a.1) _
    decide⟩
private def events : List MemoryAccess :=
  [(20000003, (Cell.register 1).addressCode, valueCode 27, valueCode 99),
   (20000002, (Cell.ram 4194304).addressCode, valueCode 0x12345678, valueCode 0xabcdef01),
   (20000001, (Cell.register 1).addressCode, valueCode 9, valueCode 27)]

theorem public_initial_image : initialImage before cells = some initial := by
  have one : (Cell.register 1).read before = .ok 9 before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok 5 before := by
    apply read_register
    simp [before]
  have ram : (Cell.ram 4194304).read before = .ok 0x12345678 before := by
    apply read_word_of_bytes
    intro i
    fin_cases i <;> simp [before, Std.ExtHashMap.getElem_insert]
  simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, one, two, ram,
    bind, Option.bind]
  rfl

theorem initial_matches : SailStateMatches cells seed before := by
  apply Proofs.initial_history_matches public_initial_image (by decide)
  exact (List.reverse_perm initial).map (fun (token : MemoryToken babyBearModulus) =>
    ((token.address, token.address, 0, token.value) : MemoryAccess))

private theorem sorted : MemoryAccessList.isTimestampSorted
    (List.append (α := MemoryAccess) events seed.val) := by
  change List.Pairwise (fun (a b : MemoryAccess) => b.1 < a.1) _
  decide

theorem derived_native_execution : ∃ after,
    SailHistory cells events before after ∧
    SailStateMatches cells ⟨List.append (α := MemoryAccess) events seed.val, sorted⟩ after := by
  apply Proofs.realize_history events seed initial_matches
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · intro event member
    simp [events] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨.register 1, by simp [cells], rfl⟩
    · exact ⟨.ram 4194304, by simp [cells], rfl⟩
    · exact ⟨.register 1, by simp [cells], rfl⟩
  · intro event member zero
    simp [events] at member
    rcases member with rfl | rfl | rfl <;> contradiction
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

theorem actual_final_reads : ∃ after,
    SailHistory cells events before after ∧
    (Cell.register 1).read after = .ok 99 after ∧
    (Cell.register 2).read after = .ok 5 after ∧
    (Cell.ram 4194304).read after = .ok 0xabcdef01 after := by
  obtain ⟨after, executed, bound⟩ := derived_native_execution
  refine ⟨after, executed, ?_, ?_, ?_⟩
  · have read := bound (.register 1) (by simp [cells])
    have last : MemoryAccessList.lastWriteValue
        (List.append (α := MemoryAccess) events seed.val) sorted
        (Cell.register 1).addressCode = valueCode 99 := rfl
    rw [last, value_code] at read
    exact read
  · have read := bound (.register 2) (by simp [cells])
    have last : MemoryAccessList.lastWriteValue
        (List.append (α := MemoryAccess) events seed.val) sorted
        (Cell.register 2).addressCode = valueCode 5 := rfl
    rw [last, value_code] at read
    exact read
  · have read := bound (.ram 4194304) (by simp [cells])
    have last : MemoryAccessList.lastWriteValue
        (List.append (α := MemoryAccess) events seed.val) sorted
        (Cell.ram 4194304).addressCode = valueCode 0xabcdef01 := rfl
    rw [last, value_code] at read
    exact read

end Tests.SailHistory
