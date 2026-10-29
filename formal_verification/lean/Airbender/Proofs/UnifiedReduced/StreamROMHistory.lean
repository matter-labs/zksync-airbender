import Airbender.Proofs.UnifiedReduced.MixedNativeROM
import Airbender.Proofs.Trace.CodeHistory

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Both ends of a native transfer name the same actual address. -/
theorem mixed_transfer_address [Fact p.Prime] (data : RequestTrace p)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.mixedSteps) :
    edge.1.address = edge.2.address := by
  rcases List.mem_append.mp member with machine | worker
  · obtain ⟨row, _, present⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp present
    rfl
  · obtain ⟨row, _, present⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp present
    rfl

/-- Interpreted ROM tokens refresh one fixed public word at either endpoint. -/
theorem interpreted_rom_refresh (initial : State) {left right : MemoryToken p}
    (same : left.address = right.address) (pc : BitVec 32)
    (inROM : pc.toNat < ROM.limit) (address : left.address = (Cell.ram pc).addressCode) :
    (Trace.ROMView.token initial left).value = (Trace.ROMView.token initial right).value := by
  have shadow : Trace.ROMView.shadow left.address := by
    rw [address]
    simp [Trace.ROMView.shadow, Cell.addressCode, Word.ofBitVec, limbBase]
    dsimp [ROM.limit] at inROM
    omega
  simp only [Trace.ROMView.token, ← same, if_pos shadow]

/-- The native ROM interpretation preserves code in the full mixed history. -/
theorem interpreted_rom_unchanged [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {native : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (accepted : MixedMemoryAccepted native program)
    (ram : ExternalBoundary.WorkerRAM.Binding native.workers.rows)
    {event : MemoryAccess}
    (member : event ∈ (NativeROM.view initial native).mixedSteps.map transferEvent)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit)
    (address : event.2.1 = (Cell.ram pc).addressCode) :
    event.2.2.1 = event.2.2.2 := by
  rw [NativeROM.Proofs.steps hp initial accepted ram, List.map_map] at member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  apply interpreted_rom_refresh initial (mixed_transfer_address native present) pc inROM
  simpa only [Function.comp_apply, transferEvent, Trace.ROMView.token_address] using address

/-- A native ROM-aware history transports public fetch without a global RAM bound. -/
theorem cycle_source_of_readonly {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {cells : List Cell} {events : List MemoryAccess} {initial before : State}
    {row : Trace.Row p UnifiedFamily} {entry : Trace.ProgramEntry Kind}
    (past : SailHistory cells
      (events.filter fun event => decide (event.1 ≤ row.clock)) initial before)
    (source : entry.SourceWith initial projection)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (pc : row.start.word.toBitVec = entry.pc) :
    entry.SourceWith (retiredState before row.start.word.toBitVec) projection := by
  have bytes := sail_history_code_frame past
    (fun event member => unchanged event (List.mem_filter.mp member).1)
    entry.pc code.1 code.2 source.bytes
  have current : entry.SourceWith before projection :=
    ⟨bytes, (decoded_misa_frame _ source.decoded).2 _
      (sail_history_control_flow_csrs past).1, source.fields⟩
  rw [pc]
  have bytes := cell_read_nextPC (.ram entry.pc) current.bytes entry.pc
  have bytes := cell_read_PC (.ram entry.pc) bytes entry.pc
  exact ⟨bytes, (decoded_misa_frame _ current.decoded).2 _
    (by simp [retiredState, Std.ExtDHashMap.get?_insert]), current.fields⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
