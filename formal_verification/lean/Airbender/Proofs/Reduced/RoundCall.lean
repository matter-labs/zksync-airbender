import Airbender.Proofs.Reduced.CallerHistory
import Airbender.Proofs.UnifiedReduced.StreamWorkerRAM
import Airbender.Proofs.Blake2Round.CallABI

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Caller Delegation.Caller.Proofs
open UnifiedReduced.Caller.Stream.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Native packing derives the round mask from the explicit controller contract. -/
theorem native_round_masks {data : RequestTrace babyBearModulus}
    {program : List PooledProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : StreamMemoryInputs data program initial ca oa cells)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows →
      ExternalBoundary.HashABI.RoundControl w) :
    ∀ row ∈ data.workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round := by
  intro row member family
  obtain ⟨family', w⟩ := row
  change family' = .blakeRound at family
  subst family'
  have core := accepted.workerConstraints ⟨.blakeRound, w⟩ member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (Blake2Round.clockConstraints data.workers.setup.blakeRound) at core
  rw [inputs.tables] at core
  have core := Verification.holds_of_sublist core
    (List.sublist_append_left (Blake2Round.importedConstraints Blake2Round.setupTable)
      Blake2Round.importedConstraintsTimestampLookups)
  obtain ⟨flags, round, _, control⟩ := controls w member
  have powerBound : 2 ^ round.val < 1024 := by fin_cases round <;> decide
  have packed : (w 136).val = flags.val + 8 * 2 ^ round.val := by
    have high := congrArg Word.hi control
    simpa [Trace.Proofs.read_word, Blake2Round.importedConstraintsMemoryPorts,
      WordColumns.evaluate, Blake2Round.controlAt, Nat.mod_eq_of_lt powerBound] using high
  exact ⟨round, (Blake2Round.Proofs.exclusive_mask_iff (by decide) core round).mpr ⟨flags, packed⟩⟩


theorem round_worker_call
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} (flags : Fin 8)
    (index : Fin (Delegation.Caller.HashSpan.blakeRound flags).callCount)
    {w : Nat → ZMod babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : StreamMemoryInputs data program initial ca oa cells)
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
    have distinct := Airbender.AddSub.Modular.External.Caller.Proofs.worker_addresses_distinct accepted inputs effects member
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


/-- Every admitted reduced worker executes its complete extended-round reference. -/
theorem native_round_worker_call
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (member : worker ∈ data.workers.rows) (family : worker.family = .blakeRound)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    UnifiedReduced.Caller.FullCall worker.family before after := by
  cases worker with
  | mk kind w =>
    cases family
    obtain ⟨flags, index, bound, control⟩ := controls w member
    exact round_worker_call flags ⟨index.val, bound⟩ accepted inputs effects ram member control
      history permutation observed

end Airbender.AddSub.Modular.External.Caller.Proofs
