import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Families.ShiftBinop.Decoder
import Airbender.Proofs.Trace.ControlFlowCSR
import Airbender.Proofs.Sail.DecoderFrame

namespace Airbender.ShiftBinop.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open Airbender.Trace.Proofs

/-- Imported v2 control ports retain the register address-space tag. -/
theorem native_event_register_space {p : Nat} [Fact p.Prime] {trace : Data p ShiftBinopFamily}
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
theorem native_history_memory {p : Nat} [Fact p.Prime] {trace : Data p ShiftBinopFamily} {cells : List Cell}
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

/-- Native history preserves both public code bytes and the actual misa image.
    Replay uses the original stateful decoder, without a new per-row premise. -/
theorem entry_source_after_native_history {p : Nat} [Fact p.Prime] {trace : Data p ShiftBinopFamily}
    {cells : List Cell} {events : List MemoryAccess} {initial before : State}
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events initial before) : entry.SourceWith before decoderFields :=
  ⟨read_word_frame (native_history_memory native history) source.bytes,
    (Reference.Sail.decoded_misa_frame _ source.decoded).2 before
      (sail_history_control_flow_csrs history).1,
    source.fields⟩

end Airbender.ShiftBinop.Proofs
