import Airbender.Review.Trace.UnifiedReduced.Paths.GPointerSeed
import Airbender.Proofs.UnifiedReduced.PathGapFrames
import Airbender.Proofs.UnifiedReduced.FullCalls

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- At G index0, the selected state/message word-zero addresses would coincide
    if their bases were equal. Native strict history excludes that coincidence,
    deriving base separation without fixing either pointer value. -/
theorem path_g_index_zero_pointer_separation
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {reduced : Bool}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    {w : Nat → ZMod babyBearModulus} (member : (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (control : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word = Blake2G.controlAt reduced 0) :
    (Blake2G.Native.statePointer w).toBitVec ≠ (Blake2G.Native.messagePointer w).toBitVec := by
  have effects := mixed_memory_effects accepted inputs
  have bounds (port : MemoryPort) (present : port ∈ Blake2G.importedConstraintsMemoryPorts) :
      (readToken w port).word.Bounded := (effects.words _ (mixed_worker_member member present)).1
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2G.clockConstraints data.workers.setup.blakeG) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows))
      Blake2G.importedConstraintsTimestampLookups)
  have active : w 0 = 1 := accepted.workerActive _ member
  let register := (Blake2G.controllerAt reduced 0).register
  have binding : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word = ⟨register.val, 0⟩ := control
  have pointerWords : Blake2G.Native.statePointer w = ⟨(w 13).val, (w 14).val⟩ ∧
      Blake2G.Native.messagePointer w = ⟨(w 31).val, (w 32).val⟩ := by
    simp [Blake2G.Native.statePointer, Blake2G.Native.messagePointer, Delegation.Row.readWord,
      Delegation.Row.ports, readToken, MemoryPort.readCode, MemoryToken.word, WordColumns.code,
      Blake2G.importedConstraintsMemoryPorts]
  have bounded : (Blake2G.Native.statePointer w).Bounded ∧ (Blake2G.Native.messagePointer w).Bounded :=
    ⟨bounds _ (Array.getElem_mem (by change 0 < 9; decide)),
      bounds _ (Array.getElem_mem (by change 5 < 9; decide))⟩
  have low := congrArg Word.lo ((Blake2G.Call.Proofs.controller_words w).1.symm.trans binding)
  have mapping : Blake2G.Addresses.Mapping
      (Blake2G.Call.Proofs.nativeArguments register w).addresses
      (Blake2G.importedConstraintsIndirectPorts.map fun port => port.address w) w :=
    ⟨low.symm, active, pointerWords.1, pointerWords.2, rfl⟩
  have addresses := Blake2G.Addresses.Proofs.soundness (p := babyBearModulus) (by decide) (by decide)
    (Blake2G.Call.Proofs.nativeArguments register w).addresses _ w ⟨bounded, core, mapping⟩
  have codes := Blake2G.Call.Proofs.cells_projection addresses (fun port present => by
    obtain ⟨cell, _, code, _⟩ := effects.addresses _ (mixed_worker_member member present)
    exact ⟨cell, code⟩)
  have state : (Cell.ram (Blake2G.Native.statePointer w).toBitVec).addressCode =
      Blake2G.importedConstraintsMemoryPorts[1].address.code w := by
    cases reduced <;> simpa [Blake2G.Call.cells, Blake2G.Call.Proofs.nativeArguments,
      Blake2G.Addresses.expected, register, Blake2G.controllerAt, Blake2G.controlAt, Blake2G.callCount,
      Blake2G.Control.step, Blake2G.Control.stateLanes, Blake2G.Control.messageSchedule] using codes 1
  have message : (Cell.ram (Blake2G.Native.messagePointer w).toBitVec).addressCode =
      Blake2G.importedConstraintsMemoryPorts[6].address.code w := by
    cases reduced <;> simpa [Blake2G.Call.cells, Blake2G.Call.Proofs.nativeArguments,
      Blake2G.Addresses.expected, register, Blake2G.controllerAt, Blake2G.controlAt, Blake2G.callCount,
      Blake2G.Control.step, Blake2G.Control.stateLanes, Blake2G.Control.messageSchedule] using codes 6
  intro same
  have equal := state.symm.trans ((congrArg (fun address => (Cell.ram address).addressCode) same).trans message)
  have unique := worker_addresses_distinct (by decide) (by decide) accepted inputs effects.requests member
  have collision : (((⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).memorySteps).map
      fun edge => edge.1.address)[1]'(by change 1 < 9; decide) =
      (((⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).memorySteps).map
        fun edge => edge.1.address)[6]'(by change 6 < 9; decide) := equal
  have impossible := unique.getElem_inj_iff.mp collision
  omega

private theorem path_g_seed_control
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {start : Nat} {reduced : Bool}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (scope : PathCallerPreparation data (start + 4) .blakeG)
    (flow : PathControllerDataflow data program start 12 (Blake2G.controlAt reduced 0).toBitVec)
    (aligned : start % 4 = 0)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.windowRows start (start + 4)) :
    worker.family = .blakeG ∧
      (readToken worker.assignment Blake2G.importedConstraintsMemoryPorts[8]).word = Blake2G.controlAt reduced 0 := by
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  obtain ⟨_, window⟩ := path_caller_window (by decide) (by decide) accepted inputs.publicProgram
    inputs.ordinaryProgram inputs.initialization scope (by omega)
  have family := window.family worker (by simpa using member)
  have raw := path_caller_control_read (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization unique scope (by omega) (value := (Blake2G.controlAt reduced 0).toBitVec)
    (by
      intro tokens matching
      exact path_controller_dataflow_token (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
        inputs.initialization unique inputs.tables flow (by decide) aligned (by simpa using matching))
    (by simpa using member)
  have zeroBound : 0 < (Delegation.Caller.HashSpan.blakeG reduced).callCount := by
    cases reduced <;> decide
  have canonical := path_hash_word_canonical (⟨.blakeG reduced, ⟨0, zeroBound⟩⟩ : HashCallPosition)
  refine ⟨family, ?_⟩
  simpa only [family, path_native_control_port, HashCallPosition.word] using raw.trans canonical

private theorem path_extend_frames_caller
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {lower target : Nat} {register : BitVec 5}
    (frames : PathRegisterGapFrames data program lower target register)
    (scope : PathCallerPreparation data (target + 4) .blakeG)
    (different : register ≠ 12) : PathRegisterGapFrames data program lower (target + 4) register := by
  refine ⟨frames.lowerAligned, by have := frames.upperAligned; omega,
    by have := frames.ordered; omega, frames.afterInitial, scope.beforeTerminal, ?_⟩
  intro cut afterLower beforeUpper aligned
  by_cases earlier : cut ≤ target
  · exact frames.code cut afterLower earlier aligned
  · have equal : cut = target + 4 := by have := frames.upperAligned; omega
    subst cut
    exact .caller scope different

/-- Arbitrary G pointer values are seeded at actual index0 and transported
    through public code frames. The target may be that very seed call or a
    later occurrence, with the intervening interval starting after the seed.
    The pointer values and their native inequality are conclusions. -/
theorem path_g_pointer_seed_binding
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {target : Nat}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (seed : PathGPointerSeed data program target)
    (scope : PathCallerPreparation data (target + 4) .blakeG) (aligned : target % 4 = 0)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.windowRows target (target + 4)) :
    (Blake2G.Native.statePointer worker.assignment).toBitVec ≠
      (Blake2G.Native.messagePointer worker.assignment).toBitVec := by
  cases seed with
  | atSeed reduced call flow =>
    obtain ⟨family, control⟩ := path_g_seed_control accepted inputs call flow aligned member
    cases worker with
    | mk kind w =>
      change kind = .blakeG at family
      subst kind
      exact path_g_index_zero_pointer_separation accepted inputs (List.mem_of_mem_filter member) control
  | @afterSeed start target reduced call flow stateFrames messageFrames =>
    have startAligned : start % 4 = 0 := by have := stateFrames.lowerAligned; omega
    obtain ⟨floor, window⟩ := path_caller_window (by decide) (by decide) accepted inputs.publicProgram
      inputs.ordinaryProgram inputs.initialization call (by omega)
    have count : (data.workers.windowRows start (start + 4)).length = 1 := by
      have same : (start + 4) - 4 = start := by omega
      rw [same] at window
      rw [← window.workerCount, window.machineCount]
      omega
    have notEmpty : data.workers.windowRows start (start + 4) ≠ [] := by
      intro empty
      rw [empty] at count
      simp at count
    obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil _ notEmpty
    obtain ⟨firstFamily, firstControl⟩ := path_g_seed_control accepted inputs call flow startAligned firstMember
    obtain ⟨_, targetWindow⟩ := path_caller_window (by decide) (by decide) accepted inputs.publicProgram
      inputs.ordinaryProgram inputs.initialization scope (by omega)
    have targetFamily := targetWindow.family worker (by simpa using member)
    have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
      rw [image_addresses inputs.initialization]
      exact inputs.distinct
    have firstInequality : (Blake2G.Native.statePointer first.assignment).toBitVec ≠
        (Blake2G.Native.messagePointer first.assignment).toBitVec := by
      cases first with
      | mk kind w =>
        change kind = .blakeG at firstFamily
        subst kind
        exact path_g_index_zero_pointer_separation accepted inputs (List.mem_of_mem_filter firstMember) firstControl
    have transport (register : BitVec 5) (frames : PathRegisterGapFrames data program (start + 4) target register)
        (nonzero : register ≠ 0) (notControl : register ≠ 12) (port : MemoryPort)
        (firstPort : port ∈ first.ports) (targetPort : port ∈ worker.ports)
        (firstAddress : port.address.code first.assignment = (Cell.register register).addressCode)
        (targetAddress : port.address.code worker.assignment = (Cell.register register).addressCode)
        (refresh : (first.writeToken port).value = (readToken first.assignment port).value) :
        (readToken worker.assignment port).word = (readToken first.assignment port).word := by
      have extended := path_extend_frames_caller frames scope notControl
      have included : (readToken worker.assignment port, worker.writeToken port) ∈
          data.windowSteps (start + 4) (target + 4) := by
        have range := of_decide_eq_true (List.mem_filter.mp member).2
        have lower := frames.ordered
        have native : worker ∈ data.workers.windowRows (start + 4) (target + 4) :=
          List.mem_filter.mpr ⟨List.mem_of_mem_filter member, decide_eq_true (by omega)⟩
        exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨worker, native, List.mem_map.mpr ⟨port, by simpa using targetPort, rfl⟩⟩))
      have raw := path_gap_read_value (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
        inputs.initialization unique extended nonzero
        (value := (readToken first.assignment port).value)
        (by
          intro tokens matching
          obtain ⟨present, _⟩ := path_caller_write_boundary (by decide) (by decide) accepted inputs.publicProgram
            inputs.ordinaryProgram inputs.initialization call (by omega) matching (by simpa using firstMember) firstPort
          exact ⟨first.writeToken port, present, firstAddress, refresh⟩)
        included targetAddress
      change (readToken worker.assignment port).value = (readToken first.assignment port).value at raw
      exact congrArg (fun value : Nat => (⟨(Nat.unpair value).1, (Nat.unpair value).2⟩ : Word)) raw
    have state := transport 10 stateFrames (by decide) (by decide) Blake2G.importedConstraintsMemoryPorts[0]
      (by rw [Delegation.Row.ports, firstFamily]; exact Array.getElem_mem (by decide))
      (by rw [Delegation.Row.ports, targetFamily]; exact Array.getElem_mem (by decide)) rfl rfl rfl
    have message := transport 11 messageFrames (by decide) (by decide) Blake2G.importedConstraintsMemoryPorts[5]
      (by rw [Delegation.Row.ports, firstFamily]; exact Array.getElem_mem (by decide))
      (by rw [Delegation.Row.ports, targetFamily]; exact Array.getElem_mem (by decide)) rfl rfl rfl
    change Blake2G.Native.statePointer worker.assignment = Blake2G.Native.statePointer first.assignment at state
    change Blake2G.Native.messagePointer worker.assignment = Blake2G.Native.messagePointer first.assignment at message
    rw [state, message]
    exact firstInequality

end Airbender.UnifiedReduced.Caller.Proofs
