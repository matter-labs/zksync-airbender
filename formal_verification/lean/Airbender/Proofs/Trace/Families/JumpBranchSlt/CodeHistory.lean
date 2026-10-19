import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Families.JumpBranchSlt.Decoder

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open Airbender.Trace.Proofs

/-- Imported v2 control ports retain the register address-space tag. -/
theorem native_event_register_space [Fact p.Prime] {trace : Data p JumpBranchSltFamily}
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents) :
    ∃ code, event.2.1 = Nat.pair 0 code := by
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, present⟩ := List.mem_flatMap.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
  cases row with
  | mk family w =>
    cases family
    change port ∈ importedConstraintsMemoryPorts.toList at portMember
    simp [importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- Actual initialized history identifies canonical GPR cells; native metadata
    excludes RAM, so every code byte survives even outside the tracked domain. -/
theorem native_history_memory [Fact p.Prime] {trace : Data p JumpBranchSltFamily} {cells : List Cell}
    {events : List MemoryAccess} {before after : State}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events before after) : after.mem = before.mem := by
  apply register_history_memory history
  intro event member
  obtain ⟨cell, _, address⟩ := history_address_member history member
  cases cell with
  | register index => exact ⟨index, address.symm⟩
  | ram pc =>
    obtain ⟨code, space⟩ := native_event_register_space (native event member)
    have impossible := address.trans space
    change Nat.pair 1 _ = Nat.pair 0 _ at impossible
    have different := (Nat.pair_eq_pair.mp impossible).1
    omega

/-- Public bytes are preserved by actual native GPR transfers. Successful setup
    construction supplies pure original decoder evidence for every later state. -/
theorem entry_source_after_native_history [Fact p.Prime] {trace : Data p JumpBranchSltFamily}
    {cells : List Cell} {events : List MemoryAccess} {initial before : State}
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (pureDecoder : SailRV32.Functions.encdec_backwards entry.bits = .pure entry.instruction)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events initial before) : entry.SourceWith before decoderFields :=
  ⟨read_word_frame (native_history_memory native history) source.bytes,
    by rw [pureDecoder]; rfl, source.fields⟩

end Airbender.JumpBranchSlt.Proofs
