import Slop.Trace.Family.Timestamps
import Slop.Trace.CodeHistory
import Slop.Trace.Code

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Every native transfer into the ROM address space is a readonly refresh.
    Actual SW writes are excluded by the imported equations and public domain. -/
theorem native_rom_unchanged [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit)
    (address : event.2.1 = (Cell.ram pc).addressCode) :
    event.2.2.1 = event.2.2.2 := by
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value,
      edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp member
  subst event
  change edge ∈ trace.rows.flatMap Row.memorySteps at edgeMember
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      simp [Row.ports, AddSub.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · rfl
      · rfl
      · simp [readToken, MemoryAddress.code, Cell.addressCode] at address
    | wordMemory =>
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts] at portMember
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
        have ram := (native_store_address hp inverse accepted boundary image rowMember selected).2
        have same : (Word.mk (w 25).val (w 26).val).toBitVec = pc := by
          rw [codes.2.1, codes.2.2]
          exact Word.ofBitVec_roundtrip pc
        rw [same] at ram
        omega

theorem native_history_code_frame [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial before after : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {events : List MemoryAccess} (permutation : events.Perm trace.nativeEvents)
    (history : SailHistory cells events before after)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit) (aligned : pc.toNat % 4 = 0)
    {bits : BitVec 32} (read : (Cell.ram pc).read before = .ok bits before) :
    (Cell.ram pc).read after = .ok bits after :=
  sail_history_code_frame history
    (fun _ member position rom address =>
      native_rom_unchanged hp inverse accepted boundary image (permutation.mem_iff.mp member)
        position rom address) pc inROM aligned read

theorem rom_reads_after_native_history [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial before : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    {events : List MemoryAccess} (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events initial before) : ROM.Reads before trace.rom := by
  rw [setup]
  exact rom_reads_after_history hp image aligned history
    (fun _ member pc low same => native_rom_unchanged
      (by dsimp [ROM.limit, timestampBase] at *; omega) inverse accepted boundary image
      (native _ member) pc low same)

end Airbender.Trace.Proofs
