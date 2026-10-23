import Airbender.Proofs.UnifiedReduced.PathCallABI
import Airbender.Proofs.Trace.InterleavedProjection
import Airbender.Proofs.Blake2G.CallWorkVector
import Airbender.Proofs.Blake2Round.PhysicalWords
import Airbender.Proofs.Keccak.CallPhysical

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false

/-- Readability at an actual cut follows from the public initialized image and
its real prefix history, including ordinary writes and timestamp refreshes. -/
theorem path_prefix_readable
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {earlier : List MemoryAccess} (inputs : MixedMemoryInputs data program initial ca oa cells)
    (past : SailHistory cells earlier initial before) :
    ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before := by
  apply history_cells_readable past inputs.aligned
  intro cell member
  obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell member
  exact ⟨value, read⟩

/-- Recover both observations from the real local worker history. Native address
uniqueness is retained rather than discarded in a weaker call existential. -/
theorem path_worker_observations
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {earlier events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : worker ∈ data.workers.rows) (past : SailHistory cells earlier initial before)
    (history : SailHistory cells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent)) :
    ∀ port ∈ worker.ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code worker.assignment ∧
      cell.read before = .ok (memoryWord (port.readCode worker.assignment)) before ∧
      cell.read after = .ok (memoryWord (port.writeCode worker.assignment)) after := by
  have effects := mixed_memory_effects accepted inputs
  have distinct : (events.map fun event => event.2.1).Nodup := by
    apply (permutation.map (fun event => event.2.1)).nodup_iff.mpr
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      worker_addresses_distinct (by decide) (by decide) accepted inputs effects.requests member
  have noZero : ∀ event ∈ events, event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp included)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
    exact Delegation.Proofs.port_not_zero worker (by simpa using portMember)
  have observations := Delegation.Proofs.atomic_observations history inputs.aligned noZero
    (path_prefix_readable inputs past) distinct
  intro port present
  let event := transferEvent (readToken worker.assignment port, worker.writeToken port)
  have included : event ∈ events := permutation.mem_iff.mpr (List.mem_map.mpr
    ⟨_, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩, rfl⟩)
  exact observations event included

private theorem indirect_tracked
    {data : RequestTrace babyBearModulus} {initial : State} {cells : List Cell}
    (effects : MixedMemoryEffects data initial cells) {worker : Delegation.Row babyBearModulus}
    (member : worker ∈ data.workers.rows) {port : MemoryPort} (present : port ∈ worker.ports)
    {indirect : Verification.IndirectPort} (shape : port.address = .indirect indirect) :
    Cell.ram (indirect.address worker.assignment) ∈ cells := by
  obtain ⟨cell, tracked, code, _⟩ := effects.addresses _ (mixed_worker_member member present)
  change cell.addressCode = port.address.code worker.assignment at code
  rw [shape] at code
  exact Delegation.Proofs.indirect_cell code ▸ tracked

private theorem g_core
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell} {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) := by
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2G.clockConstraints data.workers.setup.blakeG) at core
  rw [inputs.tables] at core
  exact Verification.holds_of_sublist core
    (List.sublist_append_left _ Blake2G.importedConstraintsTimestampLookups)

private theorem g_addresses {w : Nat → ZMod babyBearModulus} {reduced : Bool}
    (index : Fin (Blake2G.callCount reduced)) {state message : BitVec 32}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)))
    (active : w 0 = 1)
    (control : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word =
      Blake2G.controlAt reduced index.val)
    (pointers : Blake2G.Native.statePointer w = Word.ofBitVec state ∧
      Blake2G.Native.messagePointer w = Word.ofBitVec message) :
    Blake2G.importedConstraintsIndirectPorts.map (fun port => port.address w) =
      Blake2G.Addresses.expected
        ⟨Blake2G.controllerAt reduced index.val, Word.ofBitVec state, Word.ofBitVec message⟩ := by
  have low := congrArg Word.lo ((Blake2G.Call.Proofs.controller_words w).1.symm.trans control)
  have words : Blake2G.Native.statePointer w = ⟨(w 13).val, (w 14).val⟩ ∧
      Blake2G.Native.messagePointer w = ⟨(w 31).val, (w 32).val⟩ := by
    simp [Blake2G.Native.statePointer, Blake2G.Native.messagePointer, Delegation.Row.readWord,
      Delegation.Row.ports, readToken, MemoryPort.readCode, MemoryToken.word, WordColumns.code,
      Blake2G.importedConstraintsMemoryPorts]
  have mapping : Blake2G.Addresses.Mapping
      ⟨Blake2G.controllerAt reduced index.val, Word.ofBitVec state, Word.ofBitVec message⟩
      (Blake2G.importedConstraintsIndirectPorts.map fun port => port.address w) w :=
    ⟨low.symm, active, pointers.1.symm.trans words.1, pointers.2.symm.trans words.2, rfl⟩
  exact Blake2G.Addresses.Proofs.soundness (by decide) (by decide) _ _ w
    ⟨⟨Word.ofBitVec_bound _, Word.ofBitVec_bound _⟩, core, mapping⟩

private theorem g_state_coverage (reduced : Bool) (word : Fin 16) :
    ∃ index : Fin (Blake2G.callCount reduced), ∃ lane : Fin 4,
      (Blake2G.Control.step (Blake2G.controllerAt reduced index.val)).stateOffsets[lane] = word.val := by
  cases reduced <;> fin_cases word <;> decide +kernel

private theorem g_message_coverage (reduced : Bool) (word : Fin 16) :
    ∃ index : Fin (Blake2G.callCount reduced), ∃ lane : Fin 2,
      (Blake2G.Control.step (Blake2G.controllerAt reduced index.val)).messageOffsets[lane] = word.val := by
  cases reduced <;> fin_cases word <;> decide +kernel

/-- Complete indexed selected accesses imply both complete sixteen-word blocks
are in the one public initialized domain. Pointer equality here is a derived
internal path fact; public syntax and actual register dataflow supply it. -/
theorem g_native_tracking
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell} {reduced : Bool}
    {state message : BitVec 32} (rows : Fin (Blake2G.callCount reduced) → Nat → ZMod babyBearModulus)
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (members : ∀ i, (⟨.blakeG, rows i⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (binding : ∀ i, (readToken (rows i) Blake2G.importedConstraintsMemoryPorts[8]).word =
      Blake2G.controlAt reduced i.val)
    (pointers : ∀ i, Blake2G.Native.statePointer (rows i) = Word.ofBitVec state ∧
      Blake2G.Native.messagePointer (rows i) = Word.ofBitVec message) :
    ∀ stateBlock : Bool, ∀ word : Fin 16,
      Cell.ram ((if stateBlock then state else message) + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  have effects := mixed_memory_effects accepted inputs
  intro stateBlock word
  cases stateBlock
  · obtain ⟨index, lane, covered⟩ := g_message_coverage reduced word
    have addresses := g_addresses index (g_core accepted inputs (members index))
      (accepted.workerActive _ (members index)) (binding index) (pointers index)
    let slot : Fin 6 := ⟨4 + lane.val, by have := lane.isLt; omega⟩
    have tracked := indirect_tracked effects (members index)
      (port := Blake2G.importedConstraintsMemoryPorts[(Blake2G.Call.Proofs.indirectIndex slot).val])
      (Array.getElem_mem (Blake2G.Call.Proofs.indirectIndex slot).isLt)
      (Blake2G.Call.Proofs.indirect_shape slot)
    have address := congrArg (fun vector : Vector (BitVec 32) 6 => vector[slot]) addresses
    simp only [Vector.getElem_map, Fin.getElem_fin] at address
    change Cell.ram (Blake2G.importedConstraintsIndirectPorts[slot.val].address (rows index)) ∈ cells at tracked
    rw [address] at tracked
    simp only [Fin.getElem_fin] at covered
    fin_cases lane <;> simpa [slot, Blake2G.Addresses.expected, covered, Word.ofBitVec_roundtrip] using tracked
  · obtain ⟨index, lane, covered⟩ := g_state_coverage reduced word
    have addresses := g_addresses index (g_core accepted inputs (members index))
      (accepted.workerActive _ (members index)) (binding index) (pointers index)
    let slot : Fin 6 := ⟨lane.val, Nat.lt_trans lane.isLt (by decide)⟩
    have tracked := indirect_tracked effects (members index)
      (port := Blake2G.importedConstraintsMemoryPorts[(Blake2G.Call.Proofs.indirectIndex slot).val])
      (Array.getElem_mem (Blake2G.Call.Proofs.indirectIndex slot).isLt)
      (Blake2G.Call.Proofs.indirect_shape slot)
    have address := congrArg (fun vector : Vector (BitVec 32) 6 => vector[slot]) addresses
    simp only [Vector.getElem_map, Fin.getElem_fin] at address
    change Cell.ram (Blake2G.importedConstraintsIndirectPorts[slot.val].address (rows index)) ∈ cells at tracked
    rw [address] at tracked
    simp only [Fin.getElem_fin] at covered
    fin_cases lane <;> simpa [slot, Blake2G.Addresses.expected, covered, Word.ofBitVec_roundtrip] using tracked

private theorem round_core
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell} {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable) := by
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2Round.clockConstraints data.workers.setup.blakeRound) at core
  rw [inputs.tables] at core
  exact Verification.holds_of_sublist core
    (List.sublist_append_left _ Blake2Round.importedConstraintsTimestampLookups)

/-- One actual round row already selects every state/extended and message word;
no padding beyond the twenty-four state words is assumed initialized. -/
theorem round_native_tracking
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {state message : BitVec 32} {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (pointers : (Blake2Round.Native.input 0 w).statePointer = Word.ofBitVec state ∧
      (Blake2Round.Native.input 0 w).messagePointer = Word.ofBitVec message) :
    ∀ index : Fin 40, Cell.ram (if index.val < 24 then state + BitVec.ofNat 32 (4 * index.val)
      else message + BitVec.ofNat 32 (4 * (index.val - 24))) ∈ cells := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨round, mask⟩ := inputs.rounds _ member rfl
  have reads (port : MemoryPort) (present : port ∈ Blake2Round.importedConstraintsMemoryPorts) :
      (readToken w port).word.Bounded := (effects.words _ (mixed_worker_member member present)).1
  have effect := Blake2Round.Native.Proofs.native_effects (by decide) (by decide) round
    (round_core accepted inputs member) mask reads
  have addresses := effect.2.2.2
  change Blake2Round.importedConstraintsIndirectPorts.map (fun port => port.address w) =
    Blake2Round.Addresses.expected
      ⟨(Blake2Round.Native.input 0 w).statePointer, (Blake2Round.Native.input 0 w).messagePointer⟩ at addresses
  rw [pointers.1, pointers.2] at addresses
  intro index
  have tracked := indirect_tracked effects member
    (port := Blake2Round.importedConstraintsMemoryPorts[(Blake2Round.Call.Proofs.indirectIndex index).val])
    (Array.getElem_mem (Blake2Round.Call.Proofs.indirectIndex index).isLt)
    (Blake2Round.Call.Proofs.indirect_shape index)
  have address := congrArg (fun vector : Vector (BitVec 32) 40 => vector[index]) addresses
  simp only [Vector.getElem_map, Fin.getElem_fin] at address
  simp only [Fin.getElem_fin] at tracked
  rw [address] at tracked
  simpa only [Blake2Round.Addresses.expected, Vector.getElem_ofFn, Word.ofBitVec_roundtrip] using tracked

private theorem keccak_core
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell} {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.keccak, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints (Keccak.setupTable Keccak.Controller.rows)) := by
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Keccak.clockConstraints data.workers.setup.keccak) at core
  rw [inputs.tables] at core
  exact Verification.holds_of_sublist core
    (List.sublist_append_left _ Keccak.importedConstraintsTimestampLookups)

/-- Complete indexed Keccak accesses cover all thirty-one physical lanes and
both halves. Scratch lanes remain protected until the final logical projection. -/
theorem keccak_native_tracking
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell} {pointer : BitVec 32}
    (rows : Fin 649 → Nat → ZMod babyBearModulus)
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (members : ∀ i, (⟨.keccak, rows i⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (binding : ∀ i, (readToken (rows i) Keccak.importedConstraintsMemoryPorts[0]).word =
      ⟨(HashCallPosition.keccakControl i).packed, 0⟩)
    (pointers : ∀ i, Keccak.statePointer (rows i) = Word.ofBitVec pointer) :
    ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells := by
  have effects := mixed_memory_effects accepted inputs
  intro physical half
  obtain ⟨call, lane, covered⟩ := Keccak.Proofs.scheduled_lane_coverage physical
  have member := members call
  have reads (port : MemoryPort) (present : port ∈ Keccak.importedConstraintsMemoryPorts) :
      (readToken (rows call) port).word.Bounded := (effects.words _ (mixed_worker_member member present)).1
  have active : rows call 0 = 1 := accepted.workerActive _ member
  have effect := Keccak.Native.Proofs.native_effects (by decide) (by decide)
    (keccak_core accepted inputs member) active reads
  have control := congrArg Word.lo ((Keccak.Call.Proofs.controller_words (rows call)).1.symm.trans (binding call))
  have indices := Keccak.Proofs.scheduled_lane_indices call effect active control
  have selected : (rows call (7 + lane.val)).val = physical.val := (indices lane).trans covered
  let position : Fin 12 := ⟨2 * lane.val + half.val, by have := lane.isLt; have := half.isLt; omega⟩
  have tracked := indirect_tracked effects member
    (port := Keccak.importedConstraintsMemoryPorts[(Keccak.Call.Proofs.indirectIndex position).val])
    (Array.getElem_mem (Keccak.Call.Proofs.indirectIndex position).isLt)
    (Keccak.Call.Proofs.indirect_shape position)
  simp only [Fin.getElem_fin] at tracked
  have address := effect.addresses.addresses position
  simp only [Fin.getElem_fin] at address
  rw [address, pointers call, Word.ofBitVec_roundtrip] at tracked
  have div : position.val / 2 = lane.val := by dsimp [position]; have := half.isLt; omega
  have mod : position.val % 2 = half.val := by dsimp [position]; have := half.isLt; omega
  simpa only [div, mod, selected] using tracked

/-- The actual local G state changes the protected work vector by one existing
pure step and preserves the whole message block. Arbitrary earlier history is
retained; the pointer facts are derived outputs of public path preparation. -/
theorem g_native_view_step
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {earlier events : List MemoryAccess} {reduced : Bool} (index : Fin (Blake2G.callCount reduced))
    {state message : BitVec 32} {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (binding : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word = Blake2G.controlAt reduced index.val)
    (pointers : Blake2G.Native.statePointer w = Word.ofBitVec state ∧
      Blake2G.Native.messagePointer w = Word.ofBitVec message)
    (separation : PathGPointerBinding ⟨.blakeG, w⟩)
    (tracked : ∀ stateBlock : Bool, ∀ word : Fin 16,
      Cell.ram ((if stateBlock then state else message) + BitVec.ofNat 32 (4 * word.val)) ∈ cells)
    (past : SailHistory cells earlier initial before) (history : SailHistory cells events before after)
    (permutation : events.Perm ((⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent)) :
    (Blake2G.Proofs.physicalWords after state).map Word.value = Blake2G.WorkVector.step reduced index.val
      (Blake2G.Proofs.physicalWords before message) ((Blake2G.Proofs.physicalWords before state).map Word.value) ∧
      Blake2G.Proofs.physicalWords after message = Blake2G.Proofs.physicalWords before message := by
  have effects := mixed_memory_effects accepted inputs
  have bounds (port : MemoryPort) (present : port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports) :=
    effects.words _ (mixed_worker_member member present)
  have actual := path_worker_observations accepted inputs member past history permutation
  have observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := actual port present
    exact ⟨cell, code, read, written⟩
  have core := g_core accepted inputs member
  have active : w 0 = 1 := accepted.workerActive _ member
  have low := congrArg Word.lo ((Blake2G.Call.Proofs.controller_words w).1.symm.trans binding)
  change (w Blake2G.Variables.controlReadLo).val = (Blake2G.controlAt reduced index.val).lo at low
  have controlBound : (w Blake2G.Variables.controlReadLo).val < 256 := by
    rw [low]
    exact (Blake2G.controllerAt reduced index.val).register.isLt
  have controllerSame :
      (⟨⟨(w Blake2G.Variables.controlReadLo).val, controlBound⟩, true⟩ : Blake2G.Control.Input) =
        Blake2G.controllerAt reduced index.val := by
    congr 1
    exact Fin.ext low
  have addresses : Blake2G.Addresses.spec
      ⟨⟨⟨(w Blake2G.Variables.controlReadLo).val, controlBound⟩, true⟩,
        Word.ofBitVec state, Word.ofBitVec message⟩
      (Blake2G.importedConstraintsIndirectPorts.map fun port => port.address w) := by
    change _ = Blake2G.Addresses.expected _
    rw [controllerSame]
    exact g_addresses index core active binding pointers
  have nativeBounded : (Blake2G.Native.statePointer w).Bounded ∧
      (Blake2G.Native.messagePointer w).Bounded :=
    ⟨(bounds _ (Array.getElem_mem (by change 0 < 9; decide))).1,
      (bounds _ (Array.getElem_mem (by change 5 < 9; decide))).1⟩
  have words : Blake2G.Native.statePointer w = ⟨(w 13).val, (w 14).val⟩ ∧
      Blake2G.Native.messagePointer w = ⟨(w 31).val, (w 32).val⟩ := by
    simp [Blake2G.Native.statePointer, Blake2G.Native.messagePointer, Delegation.Row.readWord,
      Delegation.Row.ports, readToken, MemoryPort.readCode, MemoryToken.word, WordColumns.code,
      Blake2G.importedConstraintsMemoryPorts]
  have alignment := Blake2G.Proofs.pointer_alignment (by decide) (by decide) core
  have nativeAligned : (Blake2G.Native.statePointer w).toBitVec.toNat % 64 = 0 ∧
      (Blake2G.Native.messagePointer w).toBitVec.toNat % 64 = 0 := by
    rw [Word.toBitVec_toNat nativeBounded.1, Word.toBitVec_toNat nativeBounded.2, words.1, words.2]
    simpa [Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using alignment
  have stateAligned : state.toNat % 64 = 0 := by
    simpa only [pointers.1, Word.ofBitVec_roundtrip] using nativeAligned.1
  have messageAligned : message.toNat % 64 = 0 := by
    simpa only [pointers.2, Word.ofBitVec_roundtrip] using nativeAligned.2
  have separate : state ≠ message := by
    simpa only [PathGPointerBinding, pointers.1, pointers.2, Word.ofBitVec_roundtrip] using separation
  have current := Blake2G.Proofs.physical_state_step (by decide) (by decide) core active controlBound
    addresses (fun port present => (bounds port present).1) (fun port present => (bounds port present).2)
    observed stateAligned messageAligned separate history permutation inputs.aligned tracked
    (path_prefix_readable inputs past)
  dsimp only at current
  rw [controllerSame] at current
  exact ⟨Blake2G.Proofs.physical_reference_step reduced index.val current.1, current.2⟩

/-- One actual extended-round history realizes the existing pure compression
step on all twenty-four state words and preserves every message word. -/
theorem round_native_view_step
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {earlier events : List MemoryAccess} (flags : Fin 8)
    (index : Fin (Delegation.Caller.HashSpan.blakeRound flags).callCount)
    {state message : BitVec 32} {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (binding : (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word =
      Blake2Round.controlAt flags index.val)
    (pointers : (Blake2Round.Native.input 0 w).statePointer = Word.ofBitVec state ∧
      (Blake2Round.Native.input 0 w).messagePointer = Word.ofBitVec message)
    (past : SailHistory cells earlier initial before) (history : SailHistory cells events before after)
    (permutation : events.Perm ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent)) :
    Blake2Round.Proofs.physicalState after state = Blake2Round.Compression.step flags (Fin.ofNat 10 index.val)
      (Blake2Round.Proofs.physicalState before state) (Blake2Round.Proofs.blockWords before message 16 0) ∧
    Blake2Round.Proofs.blockWords after message 16 0 = Blake2Round.Proofs.blockWords before message 16 0 := by
  have effects := mixed_memory_effects accepted inputs
  have bounds (port : MemoryPort) (present : port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports) :=
    effects.words _ (mixed_worker_member member present)
  have actual := path_worker_observations accepted inputs member past history permutation
  have observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := actual port present
    exact ⟨cell, code, read, written⟩
  have core := round_core accepted inputs member
  have bound := index.isLt
  change index.val < (if flags.val % 2 = 1 then 7 else 10) at bound
  have indexTen : index.val < 10 := by split_ifs at bound <;> omega
  let round : Fin 10 := Fin.ofNat 10 index.val
  have roundVal : round.val = index.val := Nat.mod_eq_of_lt indexTen
  have powerBound : 2 ^ index.val < 1024 := by
    rw [← roundVal]
    exact Blake2Round.Call.Proofs.round_power_bound round
  have packed : (Blake2Round.Native.input round w).controller =
      ⟨0, flags.val + 8 * 2 ^ round.val⟩ := by
    change (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word = _
    simpa only [Blake2Round.controlAt, Nat.mod_eq_of_lt powerBound, roundVal] using binding
  have mapping := Blake2Round.Native.Proofs.native_mapping round core
  have high := congrArg Word.hi (mapping.controller.inputWord.symm.trans packed)
  have mask := Blake2Round.Proofs.exclusive_mask (by decide) core flags round high
  have modeBits := Blake2Round.Proofs.control_flags (by decide) core flags round high
  have reducedValue := (congrArg ZMod.val mapping.reduced).symm.trans modeBits.1
  have rightValue := (congrArg ZMod.val mapping.inputIsRight).symm.trans modeBits.2.1
  have compressionValue := (congrArg ZMod.val mapping.compression).symm.trans modeBits.2.2
  have modes : (Blake2Round.Native.input round w).reducedRounds = decide (flags.val % 2 = 1) ∧
      (Blake2Round.Native.input round w).inputIsRight = decide (flags.val / 2 % 2 = 1) ∧
      (Blake2Round.Native.input round w).compression = decide (flags.val / 4 = 1) := by
    cases reduced : (Blake2Round.Native.input round w).reducedRounds <;>
      cases right : (Blake2Round.Native.input round w).inputIsRight <;>
      cases compression : (Blake2Round.Native.input round w).compression
    all_goals simp only [reduced, right, compression, Bool.false_eq_true, if_false, if_true,
      ZMod.val_zero, ZMod.val_one] at reducedValue rightValue compressionValue ⊢
    all_goals simp [show flags.val % 2 = _ from reducedValue.symm,
      show flags.val / 2 % 2 = _ from rightValue.symm, show flags.val / 4 = _ from compressionValue.symm]
  have effect := Blake2Round.Native.Proofs.native_effects (by decide) (by decide) round core mask
    (fun port present => (bounds port present).1)
  have nativeWords := Blake2Round.Proofs.native_word_observations effect.2.2.2
    (fun port present => (bounds port present).1) (fun port present => (bounds port present).2) observed
  have physicalWords : ∀ i : Fin 40,
      let address := if i.val < 24 then state + BitVec.ofNat 32 (4 * i.val)
        else message + BitVec.ofNat 32 (4 * (i.val - 24))
      Delegation.Proofs.ramWord before address =
        ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).readWord (Blake2Round.Proofs.wordIndex i)).value ∧
      Delegation.Proofs.ramWord after address =
        ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).writtenWord (Blake2Round.Proofs.wordIndex i)).value := by
    intro i
    have pointersAtRound : (Blake2Round.Native.input round w).statePointer = Word.ofBitVec state ∧
        (Blake2Round.Native.input round w).messagePointer = Word.ofBitVec message := pointers
    have current := nativeWords i
    simp only [Blake2Round.Addresses.expected, Vector.getElem_ofFn, Fin.getElem_fin] at current
    simp only [pointersAtRound.1, pointersAtRound.2, Word.ofBitVec_roundtrip] at current
    exact current
  have words := Blake2Round.Proofs.physical_row_words round
    (Blake2Round.Proofs.native_encoded_words
      (fun port present => (bounds port present).1) (fun port present => (bounds port present).2) physicalWords)
  have stateBound (i : Fin 8) : (Blake2Round.Native.output w).state[i].Bounded := by
    rw [words.2.2.2.1]
    simpa only [Blake2Round.Proofs.physicalState, Blake2Round.Proofs.blockWords,
      Fin.getElem_fin, Vector.getElem_ofFn, Delegation.Proofs.ramEncoding] using
      Word.ofBitVec_bound (BitVec.ofNat 32 (Delegation.Proofs.ramWord after
        (state + BitVec.ofNat 32 (4 * (0 + i.val)))))
  have extendedBound (i : Fin 16) : (Blake2Round.Native.output w).extended[i].Bounded := by
    rw [words.2.2.2.2.1]
    simpa only [Blake2Round.Proofs.physicalState, Blake2Round.Proofs.blockWords,
      Fin.getElem_fin, Vector.getElem_ofFn, Delegation.Proofs.ramEncoding] using
      Word.ofBitVec_bound (BitVec.ofNat 32 (Delegation.Proofs.ramWord after
        (state + BitVec.ofNat 32 (4 * (8 + i.val)))))
  have result := Blake2Round.Proofs.row_compression effect modes stateBound extendedBound
  rw [words.1, words.2.1, words.2.2.1, words.2.2.2.1, words.2.2.2.2.1] at result
  exact ⟨result, words.2.2.2.2.2.symm⟩

/-- One actual Keccak local history changes all thirty-one physical lanes by
one existing pure micro-step. Untouched scratch/data lanes use real frame reads. -/
theorem keccak_native_view_step
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {earlier events : List MemoryAccess} (index : Fin 649) {pointer : BitVec 32}
    {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (member : (⟨.keccak, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (binding : (readToken w Keccak.importedConstraintsMemoryPorts[0]).word =
      ⟨(HashCallPosition.keccakControl index).packed, 0⟩)
    (pointers : Keccak.statePointer w = Word.ofBitVec pointer)
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (past : SailHistory cells earlier initial before) (history : SailHistory cells events before after)
    (permutation : events.Perm ((⟨.keccak, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent)) :
    Keccak.Proofs.physicalLanes after pointer =
      Keccak.Proofs.microStep index (Keccak.Proofs.physicalLanes before pointer) := by
  have effects := mixed_memory_effects accepted inputs
  have bounds (port : MemoryPort) (present : port ∈ (⟨.keccak, w⟩ : Delegation.Row babyBearModulus).ports) :=
    effects.words _ (mixed_worker_member member present)
  have actual := path_worker_observations accepted inputs member past history permutation
  have observed : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row babyBearModulus).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := actual port present
    exact ⟨cell, code, read, written⟩
  have active : w 0 = 1 := accepted.workerActive _ member
  have effect := Keccak.Native.Proofs.native_effects (by decide) (by decide)
    (keccak_core accepted inputs member) active (fun port present => (bounds port present).1)
  have control := congrArg Word.lo ((Keccak.Call.Proofs.controller_words w).1.symm.trans binding)
  have indices := Keccak.Proofs.scheduled_lane_indices index effect active control
  have lanes : ∀ lane : Fin 6,
      Keccak.Native.readLane w lane = Delegation.Proofs.ramLane before
        (pointer + BitVec.ofNat 32 (8 * (Keccak.Proofs.slotIndices index)[lane.val])) ∧
      Keccak.Native.writtenLane w lane = Delegation.Proofs.ramLane after
        (pointer + BitVec.ofNat 32 (8 * (Keccak.Proofs.slotIndices index)[lane.val])) := by
    intro lane
    have current := Keccak.Proofs.native_lane_observations effect.addresses
      (fun port present => (bounds port present).1) (fun port present => (bounds port present).2) observed lane
    rw [pointers, Word.ofBitVec_roundtrip, indices lane] at current
    exact current
  exact Keccak.Proofs.native_physical_step index effect active control pointers history permutation
    inputs.aligned tracked (path_prefix_readable inputs past) lanes

end Airbender.UnifiedReduced.Caller.Proofs
