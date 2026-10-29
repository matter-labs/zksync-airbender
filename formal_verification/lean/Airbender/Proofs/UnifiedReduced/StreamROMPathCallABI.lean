import Airbender.Proofs.UnifiedReduced.StreamROMWorkerABI
import Airbender.Proofs.UnifiedReduced.PathCallABI

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option Elab.async false

private theorem aligned_base_ram (pointer : BitVec 32) (offset : Nat)
    (small : offset < 64) (aligned : pointer.toNat % 64 = 0)
    (access : ROM.limit ≤ (pointer + BitVec.ofNat 32 offset).toNat) :
    ROM.limit ≤ pointer.toNat := by
  by_contra outside
  have below : pointer.toNat < ROM.limit := by omega
  have blockBound : pointer.toNat + 64 ≤ ROM.limit := by
    norm_num [ROM.limit] at below ⊢
    omega
  have offsetBound : offset < 2 ^ 32 := by omega
  have sumBound : pointer.toNat + offset < 2 ^ 32 := by
    norm_num [ROM.limit] at below
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound,
    Nat.mod_eq_of_lt sumBound] at access
  omega

private theorem g_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {reduced : Bool} (index : Fin (Blake2G.callCount reduced))
    {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (member : (⟨.blakeG, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (control : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word =
      Blake2G.controlAt reduced index.val)
    (pointers : PathGPointerBinding ⟨.blakeG, w⟩)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm ((⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent))
    (observed : ∀ port ∈ Blake2G.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) :
    Blake2G.Call.Executes before after := by
  have bounds (port : MemoryPort) (present : port ∈ Blake2G.importedConstraintsMemoryPorts) :
      (readToken w port).word.Bounded ∧
        ((⟨.blakeG, w⟩ : Delegation.Row babyBearModulus).writeToken port).word.Bounded :=
    effects.words _ (mixed_worker_member member present)
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2G.clockConstraints data.workers.setup.blakeG) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows))
      Blake2G.importedConstraintsTimestampLookups)
  have active : w 0 = 1 := accepted.workerActive _ member
  let register := (Blake2G.controllerAt reduced index.val).register
  have binding : (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word =
      ⟨register.val, 0⟩ := control
  have pointerWords : Blake2G.Native.statePointer w = ⟨(w 13).val, (w 14).val⟩ ∧
      Blake2G.Native.messagePointer w = ⟨(w 31).val, (w 32).val⟩ := by
    simp [Blake2G.Native.statePointer, Blake2G.Native.messagePointer, Delegation.Row.readWord,
      Delegation.Row.ports, readToken, MemoryPort.readCode, MemoryToken.word, WordColumns.code,
      Blake2G.importedConstraintsMemoryPorts]
  have bounded : (Blake2G.Native.statePointer w).Bounded ∧
      (Blake2G.Native.messagePointer w).Bounded :=
    ⟨(bounds _ (Array.getElem_mem (by change 0 < 9; decide))).1,
      (bounds _ (Array.getElem_mem (by change 5 < 9; decide))).1⟩
  have alignment := Blake2G.Proofs.pointer_alignment (by decide) (by decide) core
  have aligned : (Blake2G.Native.statePointer w).toBitVec.toNat % 64 = 0 ∧
      (Blake2G.Native.messagePointer w).toBitVec.toNat % 64 = 0 := by
    rw [Word.toBitVec_toNat bounded.1, Word.toBitVec_toNat bounded.2,
      pointerWords.1, pointerWords.2]
    simpa [Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using alignment
  have low := congrArg Word.lo ((Blake2G.Call.Proofs.controller_words w).1.symm.trans binding)
  have mapping : Blake2G.Addresses.Mapping
      (Blake2G.Call.Proofs.nativeArguments register w).addresses
      (Blake2G.importedConstraintsIndirectPorts.map fun port => port.address w) w :=
    ⟨low.symm, active, pointerWords.1, pointerWords.2, rfl⟩
  have addresses := Blake2G.Addresses.Proofs.soundness (p := babyBearModulus) (by decide) (by decide)
    (Blake2G.Call.Proofs.nativeArguments register w).addresses _ w ⟨bounded, core, mapping⟩
  have codes := Blake2G.Call.Proofs.cells_projection addresses (fun port present => by
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩)
  have accessState : ROM.limit ≤ ((Blake2G.Native.statePointer w).toBitVec + BitVec.ofNat 32
      (4 * (Blake2G.Control.step ⟨register, true⟩).stateOffsets[0])).toNat := by
    apply worker_cell_ram_of_binding ram member (Array.getElem_mem (by change 1 < 9; decide))
    simpa [Delegation.Row.ports, Blake2G.Call.cells, Blake2G.Call.Proofs.nativeArguments,
      Blake2G.Addresses.expected, Fin.getElem_fin] using codes 1
  have accessMessage : ROM.limit ≤ ((Blake2G.Native.messagePointer w).toBitVec + BitVec.ofNat 32
      (4 * (Blake2G.Control.step ⟨register, true⟩).messageOffsets[0])).toNat := by
    apply worker_cell_ram_of_binding ram member (Array.getElem_mem (by change 6 < 9; decide))
    simpa [Delegation.Row.ports, Blake2G.Call.cells, Blake2G.Call.Proofs.nativeArguments,
      Blake2G.Addresses.expected, Fin.getElem_fin] using codes 6
  have abi : Blake2G.Call.ABI (Blake2G.Call.Proofs.nativeArguments register w).addresses := by
    refine ⟨rfl, Blake2G.Call.Proofs.scheduled_counter reduced index.val, bounded, ?_, aligned, pointers⟩
    have stateSmall : 4 * (Blake2G.Control.step ⟨register, true⟩).stateOffsets[0] < 64 := by
      have boundedOffset := Blake2G.Control.Proofs.state_offsets_bounded ⟨register, true⟩ 0
      simp only [Fin.getElem_fin, Fin.val_zero] at boundedOffset
      omega
    have messageSmall : 4 * (Blake2G.Control.step ⟨register, true⟩).messageOffsets[0] < 64 := by
      have boundedOffset := Blake2G.Control.Proofs.message_offsets_bounded ⟨register, true⟩ 0
      simp only [Fin.getElem_fin, Fin.val_zero] at boundedOffset
      omega
    exact ⟨aligned_base_ram _ _ stateSmall aligned.1 accessState,
      aligned_base_ram _ _ messageSmall aligned.2 accessMessage⟩
  exact Blake2G.Call.Proofs.executes (by decide) (by decide) core abi active binding bounds
    history permutation observed

private theorem round_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} (flags : Fin 8)
    (index : Fin (Delegation.Caller.HashSpan.blakeRound flags).callCount)
    {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (member : (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (control : (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word =
      Blake2Round.controlAt flags index.val)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent))
    (observed : ∀ port ∈ Blake2Round.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) :
    Blake2Round.Call.Executes before after := by
  have bounds (port : MemoryPort) (present : port ∈ Blake2Round.importedConstraintsMemoryPorts) :
      (readToken w port).word.Bounded ∧
        ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).writeToken port).word.Bounded :=
    effects.words _ (mixed_worker_member member present)
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2Round.clockConstraints data.workers.setup.blakeRound) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left (Blake2Round.importedConstraints Blake2Round.setupTable)
      Blake2Round.importedConstraintsTimestampLookups)
  have indexBound := index.isLt
  change index.val < (if flags.val % 2 = 1 then 7 else 10) at indexBound
  let round : Fin 10 := ⟨index.val, by split_ifs at indexBound <;> omega⟩
  have powerBound : 2 ^ index.val < 1024 :=
    Blake2Round.Call.Proofs.round_power_bound round
  have packed : (Blake2Round.Native.input round w).controller =
      ⟨0, flags.val + 8 * 2 ^ round.val⟩ := by
    change (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word = _
    simpa only [Blake2Round.controlAt, Nat.mod_eq_of_lt powerBound] using control
  have mapping := Blake2Round.Native.Proofs.native_mapping round core
  have high := congrArg Word.hi (mapping.controller.inputWord.symm.trans packed)
  have mask := Blake2Round.Proofs.exclusive_mask (by decide) core flags round high
  have modeBits := Blake2Round.Proofs.control_flags (by decide) core flags round high
  have reducedValue := (congrArg ZMod.val mapping.reduced).symm.trans modeBits.1
  have rightValue := (congrArg ZMod.val mapping.inputIsRight).symm.trans modeBits.2.1
  have compressionValue := (congrArg ZMod.val mapping.compression).symm.trans modeBits.2.2
  have recovered : Blake2Round.Call.flags (Blake2Round.Native.input round w) = flags.val := by
    unfold Blake2Round.Call.flags
    cases reduced : (Blake2Round.Native.input round w).reducedRounds <;>
      cases right : (Blake2Round.Native.input round w).inputIsRight <;>
      cases compression : (Blake2Round.Native.input round w).compression
    all_goals simp only [reduced, right, compression, Bool.false_eq_true, Bool.toNat, Bool.cond_false, Bool.cond_true,
      if_false, if_true, ZMod.val_zero, ZMod.val_one] at reducedValue rightValue compressionValue ⊢
    all_goals have := flags.isLt
    all_goals omega
  have reducedMode : (Blake2Round.Native.input round w).reducedRounds = decide (flags.val % 2 = 1) := by
    cases mode : (Blake2Round.Native.input round w).reducedRounds
    all_goals simp only [mode, Bool.false_eq_true, if_false, if_true,
      ZMod.val_zero, ZMod.val_one] at reducedValue
    · simp [show flags.val % 2 ≠ 1 by omega]
    · simp [show flags.val % 2 = 1 from reducedValue.symm]
  have nativeEffect := Blake2Round.Native.Proofs.native_effects (by decide) (by decide) round core mask
    (fun port present => (bounds port present).1)
  have codes := Blake2Round.Call.Proofs.cells_projection nativeEffect.2.2.2 (fun port present => by
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩)
  have bounded : (Blake2Round.Native.input round w).statePointer.Bounded ∧
      (Blake2Round.Native.input round w).messagePointer.Bounded :=
    ⟨(bounds _ (Array.getElem_mem (by change 0 < 43; decide))).1,
      (bounds _ (Array.getElem_mem (by change 25 < 43; decide))).1⟩
  have alignment := Blake2Round.Proofs.pointer_alignment (by decide) (by decide) core
  have aligned : (Blake2Round.Native.input round w).statePointer.toBitVec.toNat % 128 = 0 ∧
      (Blake2Round.Native.input round w).messagePointer.toBitVec.toNat % 64 = 0 := by
    rw [Word.toBitVec_toNat bounded.1, Word.toBitVec_toNat bounded.2,
      mapping.statePointer, mapping.messagePointer]
    simpa [Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using alignment
  have separate : (Blake2Round.Native.input round w).statePointer.toBitVec ≠
      (Blake2Round.Native.input round w).messagePointer.toBitVec := by
    intro same
    have left : (Cell.ram (Blake2Round.Native.input round w).statePointer.toBitVec).addressCode =
        Blake2Round.importedConstraintsMemoryPorts[1].address.code w := by
      simpa [Delegation.Row.ports, Blake2Round.Call.cells, Fin.getElem_fin] using codes 1
    have right : (Cell.ram (Blake2Round.Native.input round w).messagePointer.toBitVec).addressCode =
        Blake2Round.importedConstraintsMemoryPorts[26].address.code w := by
      simpa [Delegation.Row.ports, Blake2Round.Call.cells, Fin.getElem_fin] using codes 26
    have equal := left.symm.trans ((congrArg (fun a => (Cell.ram a).addressCode) same).trans right)
    let addresses := (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address
    have indexed : addresses.get ⟨1, by change 1 < 43; decide⟩ =
        addresses.get ⟨26, by change 26 < 43; decide⟩ := equal
    have distinct := worker_addresses_distinct accepted inputs effects member
    have impossible := congrArg Fin.val (distinct.get_inj_iff.mp indexed)
    norm_num at impossible
  have abi : Blake2Round.Call.ABI (Blake2Round.Native.input round w) := by
    refine ⟨?_, ?_, ?_, aligned, separate⟩
    · rw [recovered]; exact packed
    · rw [reducedMode]
      simpa only [Blake2Round.Native.input, round, decide_eq_true_eq] using indexBound
    · constructor
      · apply worker_cell_ram_of_binding ram member (Array.getElem_mem (by change 1 < 43; decide))
        simpa [Delegation.Row.ports, Blake2Round.Call.cells, Fin.getElem_fin] using codes 1
      · apply worker_cell_ram_of_binding ram member (Array.getElem_mem (by change 26 < 43; decide))
        simpa [Delegation.Row.ports, Blake2Round.Call.cells, Fin.getElem_fin] using codes 26
  exact Blake2Round.Call.Proofs.executes (by decide) (by decide) core mask abi bounds
    history permutation observed

private theorem keccak_call
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} (index : Fin 649) {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (member : (⟨.keccak, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows)
    (binding : (readToken w Keccak.importedConstraintsMemoryPorts[0]).word =
      ⟨(HashCallPosition.keccakControl index).packed, 0⟩)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm ((⟨.keccak, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent))
    (observed : ∀ port ∈ Keccak.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) :
    Keccak.Call.Executes before after := by
  have bounds (port : MemoryPort) (present : port ∈ Keccak.importedConstraintsMemoryPorts) :
      (readToken w port).word.Bounded ∧
        ((⟨.keccak, w⟩ : Delegation.Row babyBearModulus).writeToken port).word.Bounded :=
    effects.words _ (mixed_worker_member member present)
  have core := accepted.workerConstraints _ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Keccak.clockConstraints data.workers.setup.keccak) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left (Keccak.importedConstraints (Keccak.setupTable Keccak.Controller.rows))
      Keccak.importedConstraintsTimestampLookups)
  have active : w 0 = 1 := accepted.workerActive _ member
  have readsBound := fun port present => (bounds port present).1
  have nativeEffect := Keccak.Native.Proofs.native_effects (by decide) (by decide) core active readsBound
  have pointerBound : (Keccak.statePointer w).Bounded := by
    rw [← (Keccak.Call.Proofs.pointer_words w).1]
    exact readsBound _ (Array.getElem_mem (by change 1 < 14; decide))
  have tracked := worker_indirect_ram_of_binding ram member
    (port := Keccak.importedConstraintsMemoryPorts[2])
    (indirect := Keccak.importedConstraintsIndirectPorts[0])
    (Array.getElem_mem (by change 2 < 14; decide)) (Keccak.Call.Proofs.indirect_shape 0)
  obtain ⟨pointerRAM, alignment⟩ := Keccak.Call.Proofs.pointer_ram nativeEffect pointerBound tracked
  have abi : Keccak.Call.ABI (Keccak.Call.Proofs.nativeArguments (HashCallPosition.keccakControl index) w) := by
    refine ⟨Keccak.Call.Proofs.schedule_supported index, pointerBound, pointerRAM, alignment, ?_⟩
    intro i
    simpa only [Keccak.Call.Proofs.nativeArguments, Fin.getElem_fin, Vector.getElem_ofFn]
      using Keccak.Call.Proofs.read_lane_bound readsBound i
  exact Keccak.Call.Proofs.executes (by decide) (by decide) core active abi binding bounds
    history permutation observed

/-- Complete local successful calls at every admitted controller position.
Controller and G-pointer bindings follow from the per-trace instruction/dataflow profile and raw
matching. The actual local history fixes both states and all native reads. -/
theorem path_hash_worker_call_of_binding
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {position : HashCallPosition} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (member : worker ∈ data.workers.rows)
    (binding : HashCallPosition.NativeBinding position worker)
    (pointers : PathCallPosition.PointerBinding (.hash position) worker)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  rcases position with ⟨span, index⟩
  rcases worker with ⟨family, w⟩
  have kind := binding.1
  cases span with
  | blakeG reduced =>
    change family = .blakeG at kind
    subst family
    exact g_call index accepted inputs effects ram member binding.2 pointers history permutation observed
  | blakeRound flags =>
    change family = .blakeRound at kind
    subst family
    exact round_call flags index accepted inputs effects ram member binding.2 history permutation observed
  | keccak =>
    change family = .keccak at kind
    subst family
    exact keccak_call index accepted inputs effects ram member binding.2 history permutation observed

/-- Occurrence-local complete calls for all four families. The command binding
stays separate; no global span, reset, native output or gap-frame premise is added. -/
theorem path_worker_call_of_binding
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (commands : BigintCommands data) (position : PathCallPosition)
    (member : worker ∈ data.workers.rows)
    (binding : match position with
      | .bigint => worker.family = .bigint
      | .hash payload => HashCallPosition.NativeBinding payload worker)
    (pointers : PathCallPosition.PointerBinding position worker)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  cases position with
  | hash payload =>
    exact path_hash_worker_call_of_binding accepted inputs effects ram member binding pointers history permutation observed
  | bigint =>
    have abi := bigint_pointer_abi_of_binding accepted inputs effects ram worker member binding
    obtain ⟨command, commandBinding⟩ := commands worker member binding
    have core := accepted.workerConstraints worker member
    rcases worker with ⟨family, w⟩
    change family = .bigint at binding
    subst family
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.clockConstraints data.workers.setup.bigint) at core
    rw [inputs.tables] at core
    have core := Verification.holds_of_sublist core
      (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable) Bigint.importedConstraintsTimestampLookups)
    exact Bigint.Call.Proofs.executes (w := w) (command := command) core abi commandBinding
      history permutation observed

end Airbender.UnifiedReduced.Caller.Stream.Proofs
