import Airbender.Proofs.FullUnsigned.StandardObservations
import Airbender.Proofs.UnifiedReduced.StreamROMWorkerABI
import Airbender.Proofs.Bigint.NativeCall
import Airbender.Proofs.Blake2Round.CallABI

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open UnifiedReduced.Caller.Proofs UnifiedReduced.Caller.Stream.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

private theorem standard_bigint_abi
    {workers : List (Delegation.Row babyBearModulus)} {w : Nat → ZMod babyBearModulus}
    (ram : ExternalBoundary.WorkerRAM.Binding workers)
    (member : (⟨.bigint, w⟩ : Delegation.Row babyBearModulus) ∈ workers)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (Bigint.importedConstraints Bigint.setupTable))
    (bounds : ∀ port ∈ Bigint.importedConstraintsMemoryPorts,
      (readToken w port).word.Bounded ∧
        ((⟨.bigint, w⟩ : Delegation.Row babyBearModulus).writeToken port).word.Bounded)
    (distinct : ((⟨.bigint, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address).Nodup) :
    Bigint.Addresses.PointerABI (Bigint.Addresses.nativeInput w) := by
  have reads (i : Fin 19) : (readToken w Bigint.importedConstraintsMemoryPorts[i]).word.Bounded :=
    (bounds _ (Array.getElem_mem i.isLt)).1
  have bounds : (Bigint.Addresses.nativeInput w).left.Bounded ∧
      (Bigint.Addresses.nativeInput w).right.Bounded := ⟨reads 0, reads 9⟩
  have alignment := Bigint.Addresses.Proofs.pointer_alignment (by decide) (by decide) core
  have aligned : (Bigint.Addresses.nativeInput w).left.lo % 32 = 0 ∧
      (Bigint.Addresses.nativeInput w).right.lo % 32 = 0 := by
    simpa only [bigint_native_input] using alignment
  refine ⟨bounds, ?_, ?_, ?_⟩
  · have left := worker_indirect_ram_of_binding ram member (port := Bigint.importedConstraintsMemoryPorts[1])
      (indirect := Bigint.importedConstraintsIndirectPorts[0])
      (Array.getElem_mem (by change 1 < 19; decide)) bigint_pointer_ports.1
    have right := worker_indirect_ram_of_binding ram member (port := Bigint.importedConstraintsMemoryPorts[10])
      (indirect := Bigint.importedConstraintsIndirectPorts[8])
      (Array.getElem_mem (by change 10 < 19; decide)) bigint_pointer_ports.2
    have both := And.intro left right
    simpa [Bigint.importedConstraintsIndirectPorts, Verification.IndirectPort.address, bigint_native_input] using both
  · rw [Word.toBitVec_toNat bounds.1, Word.toBitVec_toNat bounds.2]
    simpa [Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using aligned
  · intro same
    have values := congrArg BitVec.toNat same
    rw [Word.toBitVec_toNat bounds.1, Word.toBitVec_toNat bounds.2] at values
    have words := Word.eq_of_value bounds.1 bounds.2 values
    have codes := congrArg (fun word : Word => Nat.pair 1 (Nat.pair word.lo word.hi)) words
    have roles := bigint_base_codes w
    rw [← roles.1, ← roles.2] at codes
    have unique := distinct
    have indices := unique.get_inj_iff.mp codes
    have impossible := congrArg Fin.val indices
    norm_num at impossible


private theorem standard_round_call
    {workers : List (Delegation.Row babyBearModulus)} {w : Nat → ZMod babyBearModulus}
    {before after : State} {cells : List Cell} {events : List MemoryAccess}
    (flags : Fin 8) (index : Fin (Delegation.Caller.HashSpan.blakeRound flags).callCount)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints Blake2Round.setupTable))
    (ram : ExternalBoundary.WorkerRAM.Binding workers)
    (member : (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers)
    (bounds : ∀ port ∈ Blake2Round.importedConstraintsMemoryPorts,
      (readToken w port).word.Bounded ∧
        ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).writeToken port).word.Bounded)
    (distinct : ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge => edge.1.address).Nodup)
    (control : (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word =
      Blake2Round.controlAt flags index.val)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent))
    (observed : ∀ port ∈ Blake2Round.importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) :
    Blake2Round.Call.Executes before after := by
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
  have alignment := Blake2Round.Proofs.pointer_alignment (by decide) (by decide +kernel) core
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
    have distinct := distinct
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
  exact Blake2Round.Call.Proofs.executes (by decide) (by decide +kernel) core mask abi bounds
    history permutation observed

/-- Each admitted standard worker executes its original complete memory call.
The combined native pool supplies bounds, address separation and observations.
The input command, round controller and RAM domain remain explicit. -/
theorem unrolled_full_standard_worker_call
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {origin : State} {cells : List Cell}
    (inputs : Transfer.BoundaryInputs (unrolledFullMemoryData trace workers splitWorkers) origin cells)
    (setup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (bounds : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      edge.1.word.Bounded ∧ edge.2.word.Bounded)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ workers.rows)
    (family : FullUnsigned.standardCall worker.family)
    {before after : State} {events : List MemoryAccess}
    (history : SailHistory cells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    UnifiedReduced.Caller.FullCall worker.family before after := by
  have observed := unrolled_full_standard_input_observations accepted equations active
    initialClock initialAligned facts inputs member history permutation aligned readable
  have distinct := unrolled_full_standard_addresses_distinct accepted equations active
    initialClock initialAligned facts inputs member
  have localBounds : ∀ port ∈ worker.ports,
      (readToken worker.assignment port).word.Bounded ∧ (worker.writeToken port).word.Bounded := by
    intro port included
    apply bounds (readToken worker.assignment port, worker.writeToken port) (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_))))
    exact List.mem_flatMap.mpr ⟨worker, member, List.mem_map.mpr ⟨port, by simpa using included, rfl⟩⟩
  have core := accepted.workerEquations worker member
  rcases worker with ⟨kind, w⟩
  cases kind with
  | bigint =>
    obtain ⟨command, binding⟩ := commands _ member rfl
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.clockConstraints workers.setup.bigint) at core
    rw [setup] at core
    have holds := Verification.holds_of_sublist core
      (List.sublist_append_left (Bigint.importedConstraints Bigint.setupTable) Bigint.importedConstraintsTimestampLookups)
    have abi := standard_bigint_abi ram member holds localBounds distinct
    exact Bigint.Call.Proofs.executes holds abi binding history permutation observed
  | blakeRound =>
    obtain ⟨flags, index, limit, control⟩ := controls w member
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.clockConstraints workers.setup.blakeRound) at core
    rw [setup] at core
    have holds := Verification.holds_of_sublist core
      (List.sublist_append_left (Blake2Round.importedConstraints Blake2Round.setupTable)
        Blake2Round.importedConstraintsTimestampLookups)
    exact standard_round_call flags ⟨index.val, limit⟩ holds ram member localBounds distinct control
      history permutation observed
  | blakeG | keccak => simp [FullUnsigned.standardCall] at family

end Airbender.Compiler.MachineTargets.Proofs
