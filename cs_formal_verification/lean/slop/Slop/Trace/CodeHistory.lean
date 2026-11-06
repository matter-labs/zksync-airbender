import Slop.Trace.Program
import Slop.Trace.NativeSailHistory
import Slop.Trace.Retirement
import Slop.Trace.ROM
namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Realizing the native transfers preserves every aligned public ROM word,
    including code words outside the tracked memory-cell domain. -/
theorem sail_history_code_frame {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit) (aligned : pc.toNat % 4 = 0)
    {bits : BitVec 32} (read : (Cell.ram pc).read before = .ok bits before) :
    (Cell.ram pc).read after = .ok bits after := by
  induction history with
  | nil => exact read
  | @cons event rest before middle after past cell member address old written ih =>
    have previous := ih (fun e m => unchanged e (List.mem_cons_of_mem _ m)) read
    cases cell with
    | register index =>
      obtain ⟨result, execution, memory⟩ := gpr_write_memory index (memoryWord event.2.2.2) middle
      have same := (EStateM.Result.ok.inj (execution.symm.trans written)).2
      subst result
      exact read_word_frame memory previous
    | ram destination =>
      by_cases rom : destination.toNat < ROM.limit
      · have equal := unchanged event (List.mem_cons_self) destination rom address.symm
        have stutter := cell_write_same old
        rw [equal] at stutter
        have same := (EStateM.Result.ok.inj (stutter.symm.trans written)).2
        subst after
        exact previous
      · have same := (EStateM.Result.ok.inj
          ((write_word_state middle destination (memoryWord event.2.2.2)).symm.trans written)).2
        subst after
        apply written_word_disjoint destination.toNat (memoryWord event.2.2.2) _ previous
        left
        dsimp [ROM.limit] at inROM rom
        omega

/-- A public RAM domain above ROM preserves code without any per-row premise. -/
theorem history_code_frame_of_domain {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (domain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (pc : BitVec 32) (inROM : pc.toNat < ROM.limit) (aligned : pc.toNat % 4 = 0)
    {bits : BitVec 32} (read : (Cell.ram pc).read before = .ok bits before) :
    (Cell.ram pc).read after = .ok bits after := by
  apply sail_history_code_frame history _ pc inROM aligned read
  intro event member position rom address
  obtain ⟨cell, present, code⟩ := history_address_member history member
  have same := cell_address_injective (code.trans address)
  rw [same] at present
  have bound := domain position present
  omega

/-- Preserved code bytes and the original Sail decoder's configuration frame
    establish the same fetched instruction in the later native state. -/
theorem entry_source_after_history {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)} {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    {entry : ProgramEntry Kind} (source : entry.SourceWith before projection)
    (inROM : entry.pc.toNat < ROM.limit) (aligned : entry.pc.toNat % 4 = 0) :
    entry.SourceWith after projection :=
  ⟨sail_history_code_frame history unchanged entry.pc inROM aligned source.bytes,
    (decoded_misa_frame _ source.decoded).2 _ (sail_history_config_same history),
    source.fields⟩

/-- The complete public ROM table remains a byte-read interface in later
    states. Active queries identify cells in the public aligned domain; native
    histories preserve those bytes. No per-row expected table value is supplied. -/
theorem rom_reads_after_history [Fact p.Prime] (hp : ROM.limit < p)
    {initial before : State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (image : initialImage initial cells = some tokens)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    {events : List MemoryAccess} (history : SailHistory cells events initial before)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2) :
    ROM.Reads before (ROM.table cells tokens) := by
  intro address lo hi bounded low query
  obtain ⟨member, bytes⟩ := ROM.Proofs.read_source hp image address lo hi bounded low query
  have inROM : address.toBitVec.toNat < ROM.limit := by
    rw [Word.toBitVec_toNat bounded]
    dsimp [Word.value, Word.Bounded, limbBase, ROM.limit] at *
    omega
  exact sail_history_code_frame history unchanged address.toBitVec inROM
    (aligned _ member) bytes

end Airbender.Trace.Proofs
