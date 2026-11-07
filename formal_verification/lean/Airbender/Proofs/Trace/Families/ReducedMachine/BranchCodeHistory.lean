import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Families.ReducedMachine.BranchZeroRegister
import Airbender.Proofs.Trace.ControlFlowCSR
import Airbender.Proofs.Sail.DecoderFrame

namespace Airbender.ReducedMachine.NativeBranchRegisterProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native selected-branch equations, not mixed-port metadata alone, establish
    register address space for every actual event. -/
theorem native_event_register_space {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial : State} {count logCapacity : Nat}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : BranchDecodedTrace trace setup)
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents) :
    ∃ code, event.2.1 = Nat.pair 0 code := by
  obtain ⟨edge,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨row,rowMember,present⟩ := List.mem_flatMap.mp present
  obtain ⟨port,portMember,rfl⟩ := List.mem_map.mp present
  obtain ⟨entry,_,source,query,_⟩ := NativeBranchDecoderProofs.trace_decoding image accepted decoded row rowMember
  have native := accepted.constraints row rowMember
  cases row with
  | mk family w =>
    cases family
    change port ∈ importedConstraintsMemoryPorts.toList at portMember
    have addresses := NativeBranchPortProofs.register_addresses native source.fields query
    simp [importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl
    all_goals
      first
      | exact ⟨_,addresses 0⟩
      | exact ⟨_,addresses 1⟩
      | exact ⟨_,addresses 2⟩

/-- All actual native events are GPR accesses, so code bytes are preserved
    even outside the tracked cell domain. -/
theorem native_history_memory {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial before after : State} {cells : List Cell}
    {count logCapacity : Nat} {events : List MemoryAccess}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : BranchDecodedTrace trace setup)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events before after) : after.mem = before.mem := by
  apply register_history_memory history
  intro event member
  obtain ⟨cell,_,address⟩ := history_address_member history member
  cases cell with
  | register index => exact ⟨index,address.symm⟩
  | ram pc =>
    obtain ⟨code,space⟩ := native_event_register_space image accepted decoded (native event member)
    have impossible := address.trans space
    change Nat.pair 1 _ = Nat.pair 0 _ at impossible
    have different := (Nat.pair_eq_pair.mp impossible).1
    omega

/-- Replay the original stateful decoder in a derived native instruction
    pre-state; preserved bytes and misa are conclusions, not row assumptions. -/
theorem entry_source_after_native_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {initial before : State} {cells : List Cell}
    {count logCapacity : Nat} {events : List MemoryAccess} {entry : BranchProgramEntry}
    (image : branchDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : BranchDecodedTrace trace setup)
    (source : entry.SourceWith initial branchDecoderFields)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events initial before) : entry.SourceWith before branchDecoderFields :=
  ⟨read_word_frame (native_history_memory image accepted decoded native history) source.bytes,
    (Reference.Sail.decoded_misa_frame _ source.decoded).2 before
      (sail_history_control_flow_csrs history).1,source.fields⟩

end Airbender.ReducedMachine.NativeBranchRegisterProofs
