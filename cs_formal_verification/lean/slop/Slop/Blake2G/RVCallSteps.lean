import Slop.Blake2G.RVPhysical
import Slop.Delegation.RVCallLink

/-! RV twin of `CallPhysical.call_physical_steps`, extended with what the delegate link needs: per G call, the RV
    pre/post states agree with the reference step on the work vector, keep the message block, keep every register
    but x12 (which advances along the pinned schedule) and every RAM word outside the work vector (RAM at any address,
    the shadow RAM below `ROM_END` included). -/

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- Every native G port touches x10, x11, x12 or a word of one of the two blocks. -/
theorem g_port_cell {p : Nat} {w : Nat → ZMod p} {state message : BitVec 32} {controller : Control.Input}
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    {cell : Cell} (i : Fin 9)
    (code : cell.addressCode = importedConstraintsMemoryPorts[i.val].address.code w) :
    cell = .register 10 ∨ cell = .register 11 ∨ cell = .register 12 ∨
      ∃ j : Fin 16, cell = .ram (state + BitVec.ofNat 32 (4 * j.val)) ∨
        cell = .ram (message + BitVec.ofNat 32 (4 * j.val)) := by
  have actual (l : Fin 6) := congrArg (fun values : Vector (BitVec 32) 6 => values[l]) addresses
  have lane (l : Fin 4) : importedConstraintsIndirectPorts[l.val].address w =
      state + BitVec.ofNat 32 (4 * (Control.step controller).stateOffsets[l]) := by
    have a := actual ⟨l.val, by omega⟩
    fin_cases l <;> simpa [Addresses.expected, Word.ofBitVec_roundtrip] using a
  have word (l : Fin 2) : importedConstraintsIndirectPorts[4 + l.val].address w =
      message + BitVec.ofNat 32 (4 * (Control.step controller).messageOffsets[l]) := by
    have a := actual ⟨4 + l.val, by omega⟩
    fin_cases l <;> simpa [Addresses.expected, Word.ofBitVec_roundtrip] using a
  have stateCell (l : Fin 4)
      (code : cell.addressCode = (MemoryAddress.indirect importedConstraintsIndirectPorts[l.val]).code w) :
      ∃ j : Fin 16, cell = .ram (state + BitVec.ofNat 32 (4 * j.val)) ∨
        cell = .ram (message + BitVec.ofNat 32 (4 * j.val)) := by
    refine ⟨⟨_, Control.Proofs.state_offsets_bounded controller l⟩, Or.inl ?_⟩
    rw [indirect_cell code, lane l]
  have messageCell (l : Fin 2)
      (code : cell.addressCode = (MemoryAddress.indirect importedConstraintsIndirectPorts[4 + l.val]).code w) :
      ∃ j : Fin 16, cell = .ram (state + BitVec.ofNat 32 (4 * j.val)) ∨
        cell = .ram (message + BitVec.ofNat 32 (4 * j.val)) := by
    refine ⟨⟨_, Control.Proofs.message_offsets_bounded controller l⟩, Or.inr ?_⟩
    rw [indirect_cell code, word l]
  fin_cases i
  · exact Or.inl (cell_address_injective code)
  · exact Or.inr (Or.inr (Or.inr (stateCell 0 code)))
  · exact Or.inr (Or.inr (Or.inr (stateCell 1 code)))
  · exact Or.inr (Or.inr (Or.inr (stateCell 2 code)))
  · exact Or.inr (Or.inr (Or.inr (stateCell 3 code)))
  · exact Or.inr (Or.inl (cell_address_injective code))
  · exact Or.inr (Or.inr (Or.inr (messageCell 0 code)))
  · exact Or.inr (Or.inr (Or.inr (messageCell 1 code)))
  · exact Or.inr (Or.inr (Or.inl (cell_address_injective code)))

/-- A G call's RV history leaves every register but x10/x11/x12 and every RAM word outside both blocks unchanged. -/
theorem rv_g_row_frame {p : Nat} {w : Nat → ZMod p} {state message : BitVec 32} {controller : Control.Input}
    {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (∀ r : BitVec 5, r ≠ 10 → r ≠ 11 → r ≠ 12 → after.getReg r = before.getReg r) ∧
    (∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 16, a ≠ state + BitVec.ofNat 32 (4 * j.val)) →
      (∀ j : Fin 16, a ≠ message + BitVec.ofNat 32 (4 * j.val)) → RV.read after.mem a 4 = RV.read before.mem a 4) := by
  have touched : ∀ event ∈ events, ∃ cell : Cell, cell.addressCode = event.2.1 ∧
      (cell = .register 10 ∨ cell = .register 11 ∨ cell = .register 12 ∨
        ∃ j : Fin 16, cell = .ram (state + BitVec.ofNat 32 (4 * j.val)) ∨
          cell = .ram (message + BitVec.ofNat 32 (4 * j.val))) := by
    intro event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have member : port ∈ importedConstraintsMemoryPorts := by
      simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
    obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨cell, code⟩ := observed port (by simpa only [Delegation.Row.ports] using member)
    refine ⟨cell, code, ?_⟩
    subst equal
    exact g_port_cell addresses ⟨i, bound⟩ code
  constructor
  · intro r r10 r11 r12
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.register r).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .register r := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | h | ⟨j, h | h⟩
      · exact r10 (Cell.register.inj h)
      · exact r11 (Cell.register.inj h)
      · exact r12 (Cell.register.inj h)
      · cases h
      · cases h
    have frame := rv_history_cell_frame history aligned (.register r) trivial untouched (readRV_register r before)
    rw [readRV_register] at frame
    exact Option.some.inj frame
  · intro a alignedA outsideState outsideMessage
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.ram a).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .ram a := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | h | ⟨j, h | h⟩
      · cases h
      · cases h
      · cases h
      · exact outsideState j (Cell.ram.inj h)
      · exact outsideMessage j (Cell.ram.inj h)
    have readable := readable_of_aligned (address := a) alignedA
    have frame := rv_history_cell_frame history aligned (.ram a) alignedA untouched (readRV_ram before readable)
    rw [readRV_ram after readable] at frame
    exact Option.some.inj frame

private theorem register_port {p : Nat} {w : Nat → ZMod p} {cells : List Cell} {before after : RV.State}
    {index : BitVec 5} (i : Fin 9)
    (address : importedConstraintsMemoryPorts[i.val].address.code w = (Cell.register index).addressCode)
    (ports : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧
      cell.readRV before = some (memoryWord (port.readCode w)) ∧
      cell.readRV after = some (memoryWord (port.writeCode w))) :
    before.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].readCode w) ∧
      after.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].writeCode w) := by
  obtain ⟨cell, _, code, readBefore, readAfter⟩ :=
    ports importedConstraintsMemoryPorts[i.val] (Array.getElem_mem (by change i.val < 9; omega))
  have same : cell = .register index := cell_address_injective (code.trans address)
  subst same
  rw [readRV_register] at readBefore readAfter
  exact ⟨Option.some.inj readBefore, Option.some.inj readAfter⟩

/-- Per G call (newest first): the RV pre-state `states[i + 1]` and post-state `states[i]` agree with the reference
    step on the work vector, keep the message block, every register but x12, and every RAM word outside the work
    vector; x10/x11 hold the pointers and x12 advances along the pinned schedule. -/
theorem rv_call_steps [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (after : RV.State) (states : List RV.State),
    ∃ count : states.length = data.rows.length + 1,
      (Cell.register 10).readRV initial = some statePointer ∧
      (Cell.register 11).readRV initial = some messagePointer ∧
      statePointer.toNat % 64 = 0 ∧ messagePointer.toNat % 64 = 0 ∧ statePointer ≠ messagePointer ∧
      (∀ block : Bool, ∀ word : Fin 16,
        Cell.ram ((if block then statePointer else messagePointer) + BitVec.ofNat 32 (4 * word.val)) ∈ cells) ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.RVTraceMapping data initial after cells ∧
      ∀ i : Fin data.rows.length,
        Blake2G.State.spec
          (rvPhysicalInput (scheduledController reduced (data.rows.length - 1 - i.val) (by rw [← inputs.calls]; omega))
            (states[i.val + 1]'(by omega)) statePointer messagePointer)
          (rvPhysicalWords (states[i.val]'(by omega)) statePointer) ∧
        rvPhysicalWords (states[i.val]'(by omega)) messagePointer =
          rvPhysicalWords (states[i.val + 1]'(by omega)) messagePointer ∧
        (states[i.val + 1]'(by omega)).getReg 10 = statePointer ∧
        (states[i.val + 1]'(by omega)).getReg 11 = messagePointer ∧
        (states[i.val + 1]'(by omega)).getReg 12 = (controlAt reduced (data.rows.length - 1 - i.val)).toBitVec ∧
        (states[i.val]'(by omega)).getReg 12 = (controlAt reduced (data.rows.length - 1 - i.val + 1)).toBitVec ∧
        (∀ r : BitVec 5, r ≠ 12 → (states[i.val]'(by omega)).getReg r = (states[i.val + 1]'(by omega)).getReg r) ∧
        (∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 16, a ≠ statePointer + BitVec.ofNat 32 (4 * j.val)) →
          RV.read (states[i.val]'(by omega)).mem a 4 = RV.read (states[i.val + 1]'(by omega)).mem a 4) ∧
        (states[i.val]'(by omega)).rom = (states[i.val + 1]'(by omega)).rom ∧
        (states[i.val]'(by omega)).input = (states[i.val + 1]'(by omega)).input := by
  obtain ⟨ascending, ascendingCount, after, states, count, permutation, head, last, trace, effects⟩ :=
    rv_call_state_trace hp inverse accepted inputs aligned
  have seed := inputs.toSeed
  obtain ⟨statePointer, messagePointer, stateSource, messageSource, pointers, stateAligned, messageAligned,
    separate, tracked⟩ := seed_call_block_domain hp inverse accepted seed
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted seed.memory seed.tables
    (by intro row member other; have := inputs.family row member; simp_all)
    (by intro row member other; have := inputs.family row member; simp_all)
  refine ⟨statePointer, messagePointer, after, states, count, rv_seed_register inputs.memory stateSource,
    rv_seed_register inputs.memory messageSource, stateAligned, messageAligned, separate, tracked,
    head, last, trace, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, ascendingCount] using i.isLt)
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have family := inputs.family row member
  have native : row = ⟨.blakeG, row.assignment⟩ := by
    have same : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [family] using same
  obtain ⟨_, controlRead, controlWrite, events, eventPerm, history, ports⟩ := effects i
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints (setupTable Control.controllerRows)) := by
    have h := accepted.constraints row member
    simp only [Delegation.Row.constraints, family, inputs.tables, Delegation.modeledSetup] at h
    exact Verification.holds_of_sublist h (List.sublist_append_left _ importedConstraintsTimestampLookups)
  have value := congrArg Word.lo controlRead
  have controlValue : (row.assignment Variables.controlReadLo).val =
      (controlAt reduced (data.rows.length - 1 - i.val)).lo := by
    simpa [row, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode,
      WordColumns.code, WordColumns.evaluate, Variables.controlReadLo] using value
  have callBound : data.rows.length - 1 - i.val < callCount reduced := by rw [← inputs.calls]; omega
  have controlBound : (row.assignment Variables.controlReadLo).val < 256 := by
    rw [controlValue]
    exact (scheduledController reduced _ callBound).register.isLt
  have reads : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by simpa only [← native] using bounds.reads row member
  have writes : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using bounds.writes row member
  -- the serialized inverse fixes p = BabyBear, above Blake2G's 2^25 bound
  have field : 33554432 ≤ p := by
    rw [serialized_field inverse]; unfold babyBearModulus; norm_num
  have addresses := native_addresses (by omega) inverse core (inputs.active row member) controlBound reads
  have fixed : addressInput row.assignment controlBound =
      ⟨⟨⟨(row.assignment Variables.controlReadLo).val, controlBound⟩, true⟩,
        Word.ofBitVec statePointer, Word.ofBitVec messagePointer⟩ := by
    dsimp only [addressInput]
    rw [(pointers row member).1, (pointers row member).2]
  rw [fixed] at addresses
  have nativePorts : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code row.assignment ∧
      cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
      cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
    simpa only [← native] using ports
  have observed : ∀ port ∈ (⟨.blakeG, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
        cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
    intro port present
    obtain ⟨cell, _, code, read, write⟩ := nativePorts port present
    exact ⟨cell, code, read, write⟩
  have controller : (⟨⟨(row.assignment Variables.controlReadLo).val, controlBound⟩, true⟩ : Control.Input) =
      scheduledController reduced (data.rows.length - 1 - i.val) callBound := by
    congr 1
    exact Fin.ext controlValue
  have eventPerm' : events.Perm ((Delegation.Row.mk .blakeG row.assignment).memorySteps.map transferEvent) := by
    simpa only [← native] using eventPerm
  have current := rv_physical_state_step hp inverse core (inputs.active row member) controlBound addresses reads
    writes observed stateAligned messageAligned separate history eventPerm' aligned
  rw [controller] at current
  rw [controller] at addresses
  obtain ⟨regFrame, memFrame⟩ := rv_g_row_frame addresses
    (fun port present => by obtain ⟨cell, code, _⟩ := observed port present; exact ⟨cell, code⟩)
    history eventPerm' aligned
  obtain ⟨x10Before, x10After⟩ := register_port (index := 10) 0 rfl nativePorts
  obtain ⟨x11Before, x11After⟩ := register_port (index := 11) 5 rfl nativePorts
  obtain ⟨x12Before, x12After⟩ := register_port (index := 12) 8 rfl nativePorts
  have statePort : memoryWord (importedConstraintsMemoryPorts[0].readCode row.assignment) = statePointer := by
    have pointer := congrArg Word.toBitVec (pointers row member).1
    rw [Word.ofBitVec_roundtrip] at pointer
    exact pointer
  have messagePort : memoryWord (importedConstraintsMemoryPorts[5].readCode row.assignment) = messagePointer := by
    have pointer := congrArg Word.toBitVec (pointers row member).2
    rw [Word.ofBitVec_roundtrip] at pointer
    exact pointer
  have fields := rv_history_fields history
  refine ⟨current.1, current.2, x10Before.trans statePort, x11Before.trans messagePort,
    x12Before.trans (congrArg Word.toBitVec controlRead), x12After.trans (congrArg Word.toBitVec controlWrite),
    ?_, ?_, fields.2.1, fields.2.2⟩
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
      have words := congrArg (fun words : Vector Word 16 => words[j]) current.2
      simp only [rvPhysicalWords, rvBlockWords, Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add,
        rvRamEncoding] at words
      have bits := congrArg Word.toBitVec words
      simpa only [Word.ofBitVec_roundtrip] using bits
    · exact memFrame a alignedA outsideState (fun j same => inMessage ⟨j, same⟩)

end Airbender.Blake2G.Proofs
