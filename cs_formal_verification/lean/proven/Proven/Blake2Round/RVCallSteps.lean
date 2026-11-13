module
public import Proven.Blake2Round.RVPhysical
public import Proven.Defs.Circuits.Blake2Round.Row
public import Proven.Defs.Trace.Workers.Blake2Round.Call

@[expose] public section

/-! RV twin of the per-call part of `CallCompression.call_compression`, extended with what the delegate link needs:
    per round call, the RV pre/post states agree with the reference round on both state blocks, keep the message
    block, every register but x12 (which advances along the pinned schedule) and every RAM word outside the 24 state
    words (RAM at any address, the shadow RAM below `ROM_END` included). -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem register_port {p : Nat} {w : Nat → ZMod p} {cells : List Cell} {before after : RV.State}
    {index : BitVec 5} (i : Fin 43)
    (address : importedConstraintsMemoryPorts[i.val].address.code w = (Cell.register index).addressCode)
    (ports : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧
      cell.readRV before = some (memoryWord (port.readCode w)) ∧
      cell.readRV after = some (memoryWord (port.writeCode w))) :
    before.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].readCode w) ∧
      after.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].writeCode w) := by
  obtain ⟨cell, _, code, readBefore, readAfter⟩ :=
    ports importedConstraintsMemoryPorts[i.val] (Array.getElem_mem (by change i.val < 43; omega))
  have same : cell = .register index := cell_address_injective (code.trans address)
  subst same
  rw [readRV_register] at readBefore readAfter
  exact ⟨Option.some.inj readBefore, Option.some.inj readAfter⟩

/-- Per round call (newest first): the reference round on actual RV state blocks, the kept message block, the x10/x11
    pointers and the x12 schedule, and the frame. Globally: the pointers, their alignment and separation. -/
theorem rv_call_steps [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (after : RV.State) (states : List RV.State),
    ∃ count : states.length = data.rows.length + 1,
      (Cell.register 10).readRV initial = some statePointer ∧
      (Cell.register 11).readRV initial = some messagePointer ∧
      statePointer.toNat % 128 = 0 ∧ messagePointer.toNat % 64 = 0 ∧ statePointer ≠ messagePointer ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.RVTraceMapping data initial after cells ∧
      ∀ i : Fin data.rows.length,
        rvPhysicalState (states[i.val]'(by omega)) statePointer =
          Compression.step flags (Fin.ofNat 10 (data.rows.length - 1 - i.val))
            (rvPhysicalState (states[i.val + 1]'(by omega)) statePointer)
            (rvBlockWords (states[i.val + 1]'(by omega)) messagePointer 16 0) ∧
        rvBlockWords (states[i.val]'(by omega)) messagePointer 16 0 =
          rvBlockWords (states[i.val + 1]'(by omega)) messagePointer 16 0 ∧
        (states[i.val + 1]'(by omega)).getReg 10 = statePointer ∧
        (states[i.val + 1]'(by omega)).getReg 11 = messagePointer ∧
        (states[i.val + 1]'(by omega)).getReg 12 = (controlAt flags (data.rows.length - 1 - i.val)).toBitVec ∧
        (states[i.val]'(by omega)).getReg 12 = (controlAt flags (data.rows.length - 1 - i.val + 1)).toBitVec ∧
        (∀ r : BitVec 5, r ≠ 12 → (states[i.val]'(by omega)).getReg r = (states[i.val + 1]'(by omega)).getReg r) ∧
        (∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 24, a ≠ statePointer + BitVec.ofNat 32 (4 * j.val)) →
          RV.read (states[i.val]'(by omega)).mem a 4 = RV.read (states[i.val + 1]'(by omega)).mem a 4) ∧
        (states[i.val]'(by omega)).rom = (states[i.val + 1]'(by omega)).rom ∧
        (states[i.val]'(by omega)).input = (states[i.val + 1]'(by omega)).input := by
  obtain ⟨ascending, ascendingCount, after, states, count, permutation, head, last, trace, effects⟩ :=
    rv_call_state_trace hp inverse accepted inputs aligned
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have seed := inputs.toSeed
  have matching := seed.toMatching clockBound accepted
  have masks := matching_masks clockBound accepted matching
  have modes := matching_modes clockBound accepted matching
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted seed.memory seed.tables
    (fun row member _ => masks row member)
    (by intro row member keccak; rw [inputs.family row member] at keccak; cases keccak)
  obtain ⟨statePointer, messagePointer, stateSource, messageSource, pointers⟩ :=
    seed_call_pointers clockBound accepted seed
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  -- per-row facts shared by the global and per-call parts
  have rowFacts : ∀ i : Fin data.rows.length,
      let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, ascendingCount] using i.isLt)
      ∃ round : Fin 10, round.val = data.rows.length - 1 - i.val ∧
        Row.spec (Native.input round row.assignment) (Native.output row.assignment) ∧
        (readToken row.assignment importedConstraintsMemoryPorts[42]).word =
          controlAt flags (data.rows.length - 1 - i.val) ∧
        (row.writeToken importedConstraintsMemoryPorts[42]).word =
          controlAt flags (data.rows.length - 1 - i.val + 1) ∧
        (∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports, (readToken row.assignment port).word.Bounded) ∧
        (∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
          ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded) ∧
        (∀ index : Fin 40, importedConstraintsIndirectPorts[index].address row.assignment =
          if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
          else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))) ∧
        ∃ events : List MemoryAccess,
          events.Perm ((Delegation.Row.mk .blakeRound row.assignment).memorySteps.map transferEvent) ∧
          RVHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports, ∃ cell ∈ cells,
            cell.addressCode = port.address.code row.assignment ∧
            cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
            cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
    intro i
    let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, ascendingCount] using i.isLt)
    have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
    have nativeEq : (⟨.blakeRound, row.assignment⟩ : Delegation.Row p) = row := by
      show (⟨_, _⟩ : Delegation.Row p) = row
      rw [← inputs.family row member]
    obtain ⟨round, roundIndex, _, effect, controlRead, controlWrite, events, eventPerm, history, ports⟩ :=
      effects i
    refine ⟨round, roundIndex, effect, controlRead, controlWrite, ?_, ?_,
      round_word_address effect.2.2.2 (pointers row member round), events, ?_, history, ?_⟩
    · rw [nativeEq]; exact bounds.reads row member
    · rw [nativeEq]; exact bounds.writes row member
    · rw [nativeEq]; exact eventPerm
    · rw [nativeEq]; exact ports
  have positive : 0 < data.rows.length := by rw [inputs.calls]; split_ifs <;> decide
  -- alignment and separation, from the first call
  obtain ⟨round, _, effect, _, _, reads, _, address, _, _, _, ports⟩ := rowFacts ⟨0, positive⟩
  let first := ascending.reverse[0]'(by simpa only [List.length_reverse, ascendingCount] using positive)
  have firstMember : first ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment first.assignment)
      (importedConstraints setupTable) := by
    have holds := accepted.constraints first firstMember
    simp only [Delegation.Row.constraints, inputs.family first firstMember, inputs.tables,
      Delegation.modeledSetup] at holds
    exact Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have alignment := pointer_alignment hp (by linear_combination inverse) core
  have mapping := Native.Proofs.native_mapping round core
  have statePointerWord := (pointers first firstMember round).1
  have messagePointerWord := (pointers first firstMember round).2
  rw [mapping.statePointer] at statePointerWord
  rw [mapping.messagePointer] at messagePointerWord
  have stateLow := congrArg Word.lo statePointerWord
  have messageLow := congrArg Word.lo messagePointerWord
  simp only [Word.ofBitVec, limbBase] at stateLow messageLow
  have stateAligned : statePointer.toNat % 128 = 0 := by
    have := alignment.1
    rw [stateLow, Nat.mod_mod_of_dvd _ (by decide : 128 ∣ 65536)] at this
    exact this
  have messageAligned : messagePointer.toNat % 64 = 0 := by
    have := alignment.2
    rw [messageLow, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 65536)] at this
    exact this
  have separate : statePointer ≠ messagePointer := by
    intro same
    have cellOf (j : Fin 40) : ∃ cell ∈ cells, cell.addressCode =
        (importedConstraintsMemoryPorts[wordIndex j]).address.code first.assignment ∧
        cell = .ram (importedConstraintsIndirectPorts[j].address first.assignment) := by
      have present : importedConstraintsMemoryPorts[wordIndex j] ∈
          (⟨.blakeRound, first.assignment⟩ : Delegation.Row p).ports := Array.getElem_mem (wordIndex j).isLt
      obtain ⟨cell, member, code, _, _⟩ := ports _ present
      have shape : (importedConstraintsMemoryPorts[wordIndex j]).address =
          .indirect importedConstraintsIndirectPorts[j] := by
        fin_cases j <;> rfl
      refine ⟨cell, member, code, ?_⟩
      rw [shape] at code
      exact indirect_cell code
    obtain ⟨one, _, oneCode, oneCell⟩ := cellOf 0
    obtain ⟨two, _, twoCode, twoCell⟩ := cellOf 24
    rw [address 0] at oneCell
    rw [address 24] at twoCell
    simp only [show ((0 : Fin 40) : Nat) = 0 from rfl, show ((24 : Fin 40) : Nat) = 24 from rfl] at oneCell twoCell
    have equalCells : one = two := by rw [oneCell, twoCell, same]; simp
    subst equalCells
    have equal := oneCode.symm.trans twoCode
    have unique := seed_row_addresses_distinct clockBound accepted seed.memory firstMember
    have family := inputs.family first firstMember
    have samePorts : (first.memorySteps.map fun edge => edge.1.address)[1]'(by
        simp [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts]) =
      (first.memorySteps.map fun edge => edge.1.address)[26]'(by
        simp [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts]) := by
      simpa [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts,
        wordIndex, readToken] using equal
    have impossible := unique.getElem_inj_iff.mp samePorts
    omega
  refine ⟨statePointer, messagePointer, after, states, count, rv_seed_register inputs.memory stateSource,
    rv_seed_register inputs.memory messageSource, stateAligned, messageAligned, separate, head, last, trace, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, ascendingCount] using i.isLt)
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  obtain ⟨round, roundIndex, effect, controlRead, controlWrite, reads, writes, address, events, eventPerm,
    history, ports⟩ := rowFacts i
  have observed : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
        cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
    intro port present
    obtain ⟨cell, _, code, read, write⟩ := ports port present
    exact ⟨cell, code, read, write⟩
  have words := rv_physical_row_words round
    (rv_round_word_observations effect.2.2.2 (pointers row member round) reads writes observed)
  have stateBound : ∀ index : Fin 8, (Native.output row.assignment).state[index].Bounded := by
    intro index
    rw [words.2.2.2.1]
    simp only [rvPhysicalState, rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, rvRamEncoding]
    exact Word.ofBitVec_bound _
  have extendedBound : ∀ index : Fin 16, (Native.output row.assignment).extended[index].Bounded := by
    intro index
    rw [words.2.2.2.2.1]
    simp only [rvPhysicalState, rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, rvRamEncoding]
    exact Word.ofBitVec_bound _
  have reference := row_compression effect (modes row member round) stateBound extendedBound
  rw [show (Native.input round row.assignment).round = round from rfl] at reference
  rw [words.1, words.2.1, words.2.2.1, words.2.2.2.1, words.2.2.2.2.1] at reference
  have roundEq : round = Fin.ofNat 10 (data.rows.length - 1 - i.val) := by
    apply Fin.ext
    simp only [Fin.val_ofNat]
    rw [← roundIndex, Nat.mod_eq_of_lt round.isLt]
  obtain ⟨regFrame, memFrame⟩ := rv_round_row_frame address
    (fun port present => by obtain ⟨cell, code, _⟩ := observed port present; exact ⟨cell, code⟩)
    history eventPerm aligned
  obtain ⟨x10Before, x10After⟩ := register_port (index := 10) 0 rfl ports
  obtain ⟨x11Before, x11After⟩ := register_port (index := 11) 25 rfl ports
  obtain ⟨x12Before, x12After⟩ := register_port (index := 12) 42 rfl ports
  have statePort : memoryWord (importedConstraintsMemoryPorts[0].readCode row.assignment) = statePointer := by
    have pointer := congrArg Word.toBitVec (pointers row member round).1
    rw [Word.ofBitVec_roundtrip] at pointer
    exact pointer
  have messagePort : memoryWord (importedConstraintsMemoryPorts[25].readCode row.assignment) = messagePointer := by
    have pointer := congrArg Word.toBitVec (pointers row member round).2
    rw [Word.ofBitVec_roundtrip] at pointer
    exact pointer
  have fields := rv_history_fields history
  refine ⟨?_, words.2.2.2.2.2.symm, x10Before.trans statePort, x11Before.trans messagePort,
    x12Before.trans (congrArg Word.toBitVec controlRead), x12After.trans (congrArg Word.toBitVec controlWrite),
    ?_, ?_, fields.2.1, fields.2.2⟩
  · have result := (Prod.ext_iff.mp reference)
    rw [roundEq] at result
    exact Prod.ext result.1 result.2
  · intro r r12
    by_cases r10 : r = 10
    · subst r10
      exact x10After.trans x10Before.symm
    by_cases r11 : r = 11
    · subst r11
      exact x11After.trans x11Before.symm
    exact regFrame r r10 r11 r12
  · intro a alignedA outsideState
    by_cases inMessage : ∃ j : Fin 16, a = messagePointer + BitVec.ofNat 32 (4 * j.val)
    · obtain ⟨j, rfl⟩ := inMessage
      have entry := congrArg (fun words : Vector Word 16 => words[j]) words.2.2.2.2.2
      simp only [rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add, rvRamEncoding] at entry
      have bits := congrArg Word.toBitVec entry
      simpa only [Word.ofBitVec_roundtrip] using bits.symm
    · exact memFrame a alignedA outsideState (fun j same => inMessage ⟨j, same⟩)

end Airbender.Blake2Round.Proofs
