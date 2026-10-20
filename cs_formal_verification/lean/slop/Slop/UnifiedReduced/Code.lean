import Slop.UnifiedReduced.WordROM
import Slop.UnifiedReduced.Decoder
import Slop.Trace.CodeHistory

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem native_rom_unchanged [Fact p.Prime] (hp : 131072 < p)
    {trace : UnifiedTrace p} (accepted : Accepted trace)
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit)
    (address : event.2.1 = (Cell.ram pc).addressCode) :
    event.2.2.1 = event.2.2.2 := by
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value,
      edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp member
  subst event
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  cases row with
  | mk family w =>
    cases family
    change port ∈ importedConstraintsMemoryPorts.toList at portMember
    simp [importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl
    · rfl
    · rfl
    · have codes : (w 29).val = 1 ∧
          (w 44).val = (Word.ofBitVec pc).lo ∧ (w 45).val = (Word.ofBitVec pc).hi := by
        simpa [readToken, MemoryAddress.code, pairCode, Cell.addressCode,
          importedConstraintsMemoryPorts] using address
      have store : w 29 = 1 := by
        apply ZMod.val_injective
        simpa only [ZMod.val_one] using codes.1
      have core := Verification.holds_of_sublist (accepted.constraints _ rowMember)
        (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
      change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints trace.rom) at core
      have excluded := dispatch_exclusive (by omega) core (accepted.active _ rowMember) 17 store
      have outside := (word_rom_selection hp true core (excluded 16 (by decide)) store).2 rfl
      rw [codes.2.2] at outside
      dsimp [Word.ofBitVec, limbBase, ROM.limit] at outside inROM
      omega

theorem source_after_history [Fact p.Prime] (hp : 131072 < p)
    {trace : UnifiedTrace p} (accepted : Accepted trace)
    {initial before : State} {cells : List Cell} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0) :
    entry.SourceWith before decoderFields :=
  entry_source_after_history past
    (fun event member pc inROM address => native_rom_unchanged hp accepted (native event member) pc inROM address)
    source code.1 code.2

end Airbender.UnifiedReduced.Proofs
