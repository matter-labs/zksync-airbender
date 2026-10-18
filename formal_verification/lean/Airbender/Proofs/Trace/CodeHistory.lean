import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.Program

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Actual cell writes preserve every byte below a public RAM domain. This also
    covers missing bytes and code outside the tracked cell list. -/
theorem history_byte_frame_of_domain {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    {limit : Nat} (domain : ∀ address, Cell.ram address ∈ cells → limit ≤ address.toNat)
    (key : Nat) (inside : key < limit) : after.mem[key]? = before.mem[key]? := by
  induction history with
  | nil => rfl
  | @cons event rest before middle after past cell member address old written ih =>
    cases cell with
    | register index =>
      obtain ⟨result, execution, memory⟩ := gpr_write_memory index (memoryWord event.2.2.2) middle
      have same := (EStateM.Result.ok.inj (execution.symm.trans written)).2
      subst result
      rw [memory]
      exact ih
    | ram destination =>
      have same := (EStateM.Result.ok.inj
        ((write_word_state middle destination (memoryWord event.2.2.2)).symm.trans written)).2
      subst after
      rw [written_word_outside middle destination.toNat (memoryWord event.2.2.2) key
        (Or.inl (by have lower := domain destination member; omega))]
      exact ih

/-- Byte preservation transports an actual successful word read. Its complete
    four-byte window, rather than a desired read result, must lie in the prefix. -/
theorem word_read_byte_frame {before after : State} {limit : Nat}
    (bytes : ∀ key < limit, after.mem[key]? = before.mem[key]?)
    {address : BitVec 32} (inside : address.toNat + 4 ≤ limit) {bits : BitVec 32}
    (read : (Cell.ram address).read before = .ok bits before) :
    (Cell.ram address).read after = .ok bits after := by
  apply read_word_of_bytes
  intro i
  rw [bytes (address.toNat + i.val) (by have bound := i.isLt; omega)]
  exact read_word_memory read i

/-- Adapt the source code-history frame to a byte prefix, retaining the original
    Sail reads and the pure-decoder evidence checked by public construction. -/
theorem entry_source_after_byte_frame {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before after : State} {limit : Nat}
    (bytes : ∀ key < limit, after.mem[key]? = before.mem[key]?)
    {entry : ProgramEntry Kind} (source : entry.SourceWith before projection)
    (inside : entry.pc.toNat + 4 ≤ limit)
    (pureDecoder : SailRV32.Functions.encdec_backwards entry.bits = .pure entry.instruction) :
    entry.SourceWith after projection :=
  ⟨word_read_byte_frame bytes inside source.bytes, by rw [pureDecoder]; rfl, source.fields⟩

end Airbender.Trace.Proofs
