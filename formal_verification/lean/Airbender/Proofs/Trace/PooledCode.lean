import Airbender.Proofs.Trace.PooledHistory
import Airbender.Proofs.Trace.CodeHistory

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
/-- Pooled native writes preserve public ROM. Direct register writes cannot
    address it; word/subword stores are excluded by their imported equations.
    Address bounds come from the globally initialized history. -/
theorem pooled_native_rom_unchanged {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit)
    (address : event.2.1 = (Cell.ram pc).addressCode) :
    event.2.2.1 = event.2.2.2 := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value,
      edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp member
  subst event
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      change port ∈ AddSub.importedConstraintsMemoryPorts.toList at portMember
      simp [AddSub.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · simp [readToken, MemoryAddress.code, Cell.addressCode] at address
    | jumpBranchSlt =>
      change port ∈ JumpBranchSlt.importedConstraintsMemoryPorts.toList at portMember
      simp [JumpBranchSlt.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · simp [readToken, MemoryAddress.code, Cell.addressCode] at address
    | mulDiv =>
      change port ∈ MulDiv.importedConstraintsMemoryPorts.toList at portMember
      simp [MulDiv.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · simp [readToken, MemoryAddress.code, Cell.addressCode] at address
    | shiftBinop =>
      change port ∈ ShiftBinop.importedConstraintsMemoryPorts.toList at portMember
      simp [ShiftBinop.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · simp [readToken, MemoryAddress.code, Cell.addressCode] at address
    | wordMemory =>
      change port ∈ WordMemory.importedConstraintsMemoryPorts.toList at portMember
      simp [WordMemory.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · have codes : (w 10).val = 1 ∧
            (w 25).val = (Word.ofBitVec pc).lo ∧
            (w 26).val = (Word.ofBitVec pc).hi := by
          simpa [readToken, MemoryAddress.code, pairCode, Cell.addressCode,
            WordMemory.importedConstraintsMemoryPorts] using address
        have selected : w 10 = 1 := by
          apply ZMod.val_injective
          simpa only [ZMod.val_one] using codes.1
        have bound := address_bounds clockSize inverse accepted clocks image _ rowMember
          WordMemory.importedConstraintsMemoryPorts[2]
          (by change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
              simp [WordMemory.importedConstraintsMemoryPorts])
        change (Word.mk (w 25).val (w 26).val).Bounded at bound
        have core := Verification.holds_of_sublist (accepted.constraints _ rowMember)
          (List.sublist_append_left (WordMemory.importedConstraints trace.rom.wordMemory)
            WordMemory.importedConstraintsTimestampLookups)
        have outside := (WordMemory.Proofs.rom_selection (by omega) true core selected
          (address := Word.mk (w 25).val (w 26).val) (ZMod.natCast_zmod_val _).symm bound).2 rfl
        change 64 ≤ (w 26).val at outside
        have canonical : (Word.mk (w 25).val (w 26).val).toBitVec = pc := by
          rw [codes.2.1, codes.2.2]
          exact Word.ofBitVec_roundtrip pc
        have lower : ROM.limit ≤ (Word.mk (w 25).val (w 26).val).toBitVec.toNat := by
          rw [Word.toBitVec_toNat bound]
          dsimp [ROM.limit, Word.value, limbBase]
          omega
        rw [canonical] at lower
        omega
    | subwordMemory =>
      change port ∈ SubwordMemory.importedConstraintsMemoryPorts.toList at portMember
      simp [SubwordMemory.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · have codes : (w 10).val = 1 ∧
            (w 27).val = (Word.ofBitVec pc).lo ∧
            (w 28).val = (Word.ofBitVec pc).hi := by
          simpa [readToken, MemoryAddress.code, pairCode, Cell.addressCode,
            SubwordMemory.importedConstraintsMemoryPorts] using address
        have selected : w 10 = 1 := by
          apply ZMod.val_injective
          simpa only [ZMod.val_one] using codes.1
        have bound := address_bounds clockSize inverse accepted clocks image _ rowMember
          SubwordMemory.importedConstraintsMemoryPorts[2]
          (by change SubwordMemory.importedConstraintsMemoryPorts[2] ∈ SubwordMemory.importedConstraintsMemoryPorts
              simp [SubwordMemory.importedConstraintsMemoryPorts])
        change (Word.mk (w 27).val (w 28).val).Bounded at bound
        have core := Verification.holds_of_sublist (accepted.constraints _ rowMember)
          (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
            SubwordMemory.importedConstraintsTimestampLookups)
        have outside := (SubwordMemory.Proofs.rom_selection (by omega) true core selected
          (address := Word.mk (w 27).val (w 28).val) (ZMod.natCast_zmod_val _).symm bound).2 rfl
        change 64 ≤ (w 28).val at outside
        have canonical : (Word.mk (w 27).val (w 28).val).toBitVec = pc := by
          rw [codes.2.1, codes.2.2]
          exact Word.ofBitVec_roundtrip pc
        have lower : ROM.limit ≤ (Word.mk (w 27).val (w 28).val).toBitVec.toNat := by
          rw [Word.toBitVec_toNat bound]
          dsimp [ROM.limit, Word.value, limbBase]
          omega
        rw [canonical] at lower
        omega

/-- The actual public instruction remains decodable after any earlier pooled
    history. This is the code/configuration frame needed by Sail composition. -/
theorem pooled_source_after_history {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    {before : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before) :
    entry.SourceWith before pooledDecoderFields :=
  entry_source_after_history past
    (fun event member pc rom address =>
      pooled_native_rom_unchanged hp inverse accepted clocks image
        (native event member) pc rom address)
    (run_program_sources programImage entry present) code.1 code.2

/-- Modeled word-ROM reads retain their public-byte meaning after mixed
    register/RAM writes. No expected lookup result is an input. -/
theorem pooled_rom_reads_after_history {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (setup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {before : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before) :
    ROM.Reads before trace.rom.wordMemory := by
  rw [setup]
  exact rom_reads_after_history (by dsimp [ROM.limit]; omega) image aligned past
    (fun event member pc rom address =>
      pooled_native_rom_unchanged hp inverse accepted clocks image
        (native event member) pc rom address)

end Airbender.Trace.Proofs
