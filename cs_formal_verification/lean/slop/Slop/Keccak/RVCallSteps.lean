module
public import Slop.Keccak.RVPhysical
public import Slop.Keccak.RVSpec
public import Slop.Delegation.RVCallLink
public import Slop.Keccak.RVStateTrace
public import Batteries.Data.Fin.Fold
public import Slop.Defs.Circuits.Keccak.Artifact
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Trace.Workers.Keccak.Call

@[expose] public section

/-! RV twin of `CallPhysical.call_physical_steps`, extended with what the delegate link needs: per special5 call, the
    RV pre/post states move the 31 physical lanes by `microStep`, keep every register but x10 (which advances along
    the pinned schedule) and every RAM word outside the 248-byte block (RAM at any address, the shadow RAM below
    `ROM_END` included); then one call is the spec's `keccakSpecial5` delegation (`keccak_call_link`). -/

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem register_port {p : Nat} {w : Nat → ZMod p} {cells : List Cell} {before after : RV.State}
    {index : BitVec 5} (i : Fin 14)
    (address : importedConstraintsMemoryPorts[i.val].address.code w = (Cell.register index).addressCode)
    (ports : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code w ∧
      cell.readRV before = some (memoryWord (port.readCode w)) ∧
      cell.readRV after = some (memoryWord (port.writeCode w))) :
    before.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].readCode w) ∧
      after.getReg index = memoryWord (importedConstraintsMemoryPorts[i.val].writeCode w) := by
  obtain ⟨cell, _, code, readBefore, readAfter⟩ :=
    ports importedConstraintsMemoryPorts[i.val] (Array.getElem_mem (by change i.val < 14; omega))
  have same : cell = .register index := cell_address_injective (code.trans address)
  subst same
  rw [readRV_register] at readBefore readAfter
  exact ⟨Option.some.inj readBefore, Option.some.inj readAfter⟩

private theorem control_read_word {p : Nat} (w : Nat → ZMod p) :
    memoryWord (importedConstraintsMemoryPorts[0].readCode w) =
      (Word.mk (w Variables.controlReadLo).val (w Variables.controlReadHi).val).toBitVec := by
  simp [memoryWord, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code]

private theorem control_write_word {p : Nat} (w : Nat → ZMod p) :
    memoryWord (importedConstraintsMemoryPorts[0].writeCode w) =
      (Word.mk (w Variables.controlWriteLo).val (w Variables.controlWriteHi).val).toBitVec := by
  simp [memoryWord, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code]

private theorem pointer_read_word {p : Nat} (w : Nat → ZMod p) :
    memoryWord (importedConstraintsMemoryPorts[1].readCode w) = (statePointer w).toBitVec ∧
      memoryWord (importedConstraintsMemoryPorts[1].writeCode w) = (statePointer w).toBitVec := by
  constructor <;>
    simp [memoryWord, statePointer, importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code]

private theorem word_packed (n : Nat) : (Word.mk n 0).toBitVec = BitVec.ofNat 32 n := by
  simp [Word.toBitVec, Word.value]

/-- Per special5 call (newest first): the RV pre-state `states[i + 1]` and post-state `states[i]` move the 31 physical
    lanes by `microStep`, keep every register but x10 and every RAM word outside the block; x10 advances along the
    pinned schedule and x11 holds the 256-aligned pointer. -/
theorem rv_call_steps [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (pointer : BitVec 32) (after : RV.State) (states : List RV.State), ∃ count : states.length = 650,
      (Cell.register 11).readRV initial = some pointer ∧ pointer.toNat % 256 = 0 ∧
      (∀ physical : Fin 31, ∀ half : Fin 2,
        Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells) ∧
      states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.RVTraceMapping data initial after cells ∧
      ∀ i : Fin 649,
        rvPhysicalLanes (states[i.val]'(by omega)) pointer =
          microStep ⟨648 - i.val, by omega⟩ (rvPhysicalLanes (states[i.val + 1]'(by omega)) pointer) ∧
        (states[i.val + 1]'(by omega)).getReg 10 =
          BitVec.ofNat 32 (scheduleControl ⟨648 - i.val, by omega⟩).packed ∧
        (states[i.val]'(by omega)).getReg 10 =
          BitVec.ofNat 32 (scheduleControl ⟨648 - i.val + 1, by omega⟩).packed ∧
        (states[i.val + 1]'(by omega)).getReg 11 = pointer ∧
        (∀ r : BitVec 5, r ≠ 10 → (states[i.val]'(by omega)).getReg r = (states[i.val + 1]'(by omega)).getReg r) ∧
        (∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 62, a ≠ pointer + BitVec.ofNat 32 (4 * j.val)) →
          RV.read (states[i.val]'(by omega)).mem a 4 = RV.read (states[i.val + 1]'(by omega)).mem a 4) ∧
        (states[i.val]'(by omega)).rom = (states[i.val + 1]'(by omega)).rom ∧
        (states[i.val]'(by omega)).input = (states[i.val + 1]'(by omega)).input := by
  obtain ⟨pointer, ascending, count, after, states, stateCount, pointerRead, permutation, head, last, trace,
    tracked, calls⟩ := rv_call_state_trace hp inverse accepted inputs tables aligned
  have pointerAligned : pointer.toNat % 256 = 0 := by
    obtain ⟨_, effects, _, _, _, mapped, _⟩ := calls 0
    have check := effects.addresses.aligned
    rw [mapped] at check
    simp only [Word.ofBitVec, limbBase] at check
    omega
  refine ⟨pointer, after, states, stateCount, pointerRead, pointerAligned, tracked, head, last, trace, ?_⟩
  intro i
  obtain ⟨family, effects, active, controlRead, controlWrite, mapped, reads, writes, events, eventPerm, history,
    ports⟩ := calls i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have native : row = ⟨.keccak, row.assignment⟩ := by
    rw [← family]
  have nativePorts : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code row.assignment ∧
      cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
      cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
    simpa only [← native] using ports
  have observed : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
        cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
    intro port present
    obtain ⟨cell, _, code, read, write⟩ := nativePorts port present
    exact ⟨cell, code, read, write⟩
  have nativeReads : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by simpa only [← native] using reads
  have nativeWrites : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.keccak, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using writes
  have eventPerm' : events.Perm ((Delegation.Row.mk .keccak row.assignment).memorySteps.map transferEvent) := by
    simpa only [← native] using eventPerm
  have control : (row.assignment Variables.controlReadLo).val = (scheduleControl ⟨648 - i.val, by omega⟩).packed :=
    congrArg Word.lo controlRead
  have indices := scheduled_lane_indices ⟨648 - i.val, by omega⟩ effects active control
  have lanes : ∀ lane : Fin 6,
      Native.readLane row.assignment lane = rvRamLane (states[i.val + 1]'(by omega))
        (pointer + BitVec.ofNat 32 (8 * (slotIndices ⟨648 - i.val, by omega⟩)[lane])) ∧
      Native.writtenLane row.assignment lane = rvRamLane (states[i.val]'(by omega))
        (pointer + BitVec.ofNat 32 (8 * (slotIndices ⟨648 - i.val, by omega⟩)[lane])) := by
    intro lane
    have result := rv_native_lane_observations effects.addresses nativeReads nativeWrites observed lane
    rw [mapped, Word.ofBitVec_roundtrip, indices lane] at result
    exact result
  have codes : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment := by
    intro port present
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩
  have physical := rv_native_physical_step ⟨648 - i.val, by omega⟩ effects active control mapped history
    eventPerm' aligned tracked codes lanes
  obtain ⟨regFrame, memFrame⟩ := rv_keccak_row_frame ⟨648 - i.val, by omega⟩ effects.addresses mapped indices
    codes history eventPerm' aligned
  obtain ⟨x10Before, x10After⟩ := register_port (index := 10) 0 rfl nativePorts
  obtain ⟨x11Before, x11After⟩ := register_port (index := 11) 1 rfl nativePorts
  simp only [Fin.val_zero, Fin.val_one] at x10Before x10After x11Before x11After
  have pointerWord : (statePointer row.assignment).toBitVec = pointer := by
    rw [mapped, Word.ofBitVec_roundtrip]
  have fields := rv_history_fields history
  refine ⟨physical, ?_, ?_, ?_, ?_, ?_, fields.2.1, fields.2.2⟩
  · rw [x10Before, control_read_word, controlRead, word_packed]
  · rw [x10After, control_write_word, controlWrite, word_packed]
  · rw [x11Before, (pointer_read_word _).1, pointerWord]
  · intro r r10
    by_cases r11 : r = 11
    · subst r11
      rw [x11After, x11Before, (pointer_read_word _).1, (pointer_read_word _).2]
    exact regFrame r r10 r11
  · intro a alignedA outside
    apply memFrame a alignedA
    intro lane half same
    have bound : (slotIndices ⟨648 - i.val, by omega⟩)[lane] < 31 := Controller.Proofs.rows_bound _ lane
    apply outside ⟨2 * (slotIndices ⟨648 - i.val, by omega⟩)[lane] + half.val, by
      have := half.isLt
      omega⟩
    rw [same]
    dsimp only
    rw [show 4 * (2 * (slotIndices ⟨648 - i.val, by omega⟩)[lane] + half.val) =
      8 * (slotIndices ⟨648 - i.val, by omega⟩)[lane] + 4 * half.val by omega]

/-- The two halves of a 64-bit lane whose value is `lo + 2^32 hi`. -/
theorem lane_halves (L : Spec.Lane) (lo hi : BitVec 32) (value : L.toNat = lo.toNat + 2 ^ 32 * hi.toNat) :
    L.extractLsb' 0 32 = lo ∧ L.extractLsb' 32 32 = hi := by
  have l := lo.isLt
  have h := hi.isLt
  constructor
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, value]
  all_goals omega

/-- A lane read by `readLanes` is its low word plus `2^32` times its high word. -/
theorem read_lane_toNat (mem : RV.Word → BitVec 8) (pointer : BitVec 32) (l : Fin 31) :
    (RV.readLanes mem pointer 31)[l].toNat =
      (RV.read mem (pointer + BitVec.ofNat 32 (8 * l.val)) 4).toNat +
        2 ^ 32 * (RV.read mem (pointer + BitVec.ofNat 32 (8 * l.val) + 4) 4).toNat := by
  have address : pointer + BitVec.ofNat 32 (8 * l.val + 4) = pointer + BitVec.ofNat 32 (8 * l.val) + 4 := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  have low := (RV.read mem (pointer + BitVec.ofNat 32 (8 * l.val)) 4).isLt
  simp only [RV.readLanes, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.toNat_append, address]
  rw [← Nat.shiftLeft_add_eq_or_of_lt low, Nat.shiftLeft_eq]
  ring

theorem rv_physical_lanes_read (state : RV.State) (pointer : BitVec 32) (l : Fin 31) :
    rvPhysicalLanes state pointer l = (RV.readLanes state.mem pointer 31)[l].toNat := by
  rw [read_lane_toNat]
  simp only [rvPhysicalLanes, rvRamLane, rvRamEncoding, Word.ofBitVec_value]

/-- One special5 call: the spec's delegation from the circuit's pre-state (at any PC) is its post-state. -/
theorem keccak_call_link {S T : RV.State} {pointer : BitVec 32} (call : Fin 649)
    (pointerAligned : pointer.toNat % 256 = 0)
    (physical : rvPhysicalLanes T pointer = microStep call (rvPhysicalLanes S pointer))
    (x10 : S.getReg 10 = BitVec.ofNat 32 (scheduleControl ⟨call.val, by omega⟩).packed)
    (x10' : T.getReg 10 = BitVec.ofNat 32 (scheduleControl ⟨call.val + 1, by omega⟩).packed)
    (x11 : S.getReg 11 = pointer)
    (regs : ∀ r : BitVec 5, r ≠ 10 → T.getReg r = S.getReg r)
    (words : ∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 62, a ≠ pointer + BitVec.ofNat 32 (4 * j.val)) →
      RV.read T.mem a 4 = RV.read S.mem a 4)
    (rom : T.rom = S.rom) (input : T.input = S.input) (x : RV.Word) :
    ∃ U, RV.calls [.keccak] (S.setPC x) = some U ∧ RV.Same U (T.setPC (x + 4)) := by
  have valid := schedule_valid call
  have stepNat := special5_step_nat call (RV.readLanes S.mem pointer 31)
  have nextEq := next_packed (scheduleControl ⟨call.val, by omega⟩)
  have schedNext := schedule_next call
  obtain ⟨c, hc⟩ : ∃ c, scheduleControl ⟨call.val, by omega⟩ = c := ⟨_, rfl⟩
  rw [hc] at valid stepNat nextEq schedNext x10
  obtain ⟨n, hn⟩ : ∃ n, RV.Delegation.special5Next c.mode.val c.iteration.val c.round.val = n := ⟨_, rfl⟩
  rw [hn] at nextEq
  obtain ⟨L, hL⟩ : ∃ L, RV.Delegation.special5Step c.mode.val c.iteration c.round.val
      (RV.readLanes S.mem pointer 31) = L := ⟨_, rfl⟩
  rw [hL] at stepNat
  have fits : pointer.toNat + 4 * (2 * 31) ≤ 2 ^ 32 := by have := pointer.isLt; omega
  have effect : RV.Delegation.effect .keccak ((S.setPC x).getReg 10) ((S.setPC x).getReg 11)
      ((S.setPC x).getReg 12) (S.setPC x).mem =
      some { writes := RV.writesAt pointer (RV.laneWords L), reg := 10, val := RV.Delegation.control n.1 n.2.1 n.2.2 } := by
    change RV.Delegation.keccakSpecial5 (S.getReg 10) (S.getReg 11) S.mem = _
    rw [x10, x11, ← hL]
    have mode := c.mode.isLt
    have column := c.iteration.isLt
    exact RV.keccakCall_ctl (fun op _ _ => op < 7) RV.Delegation.special5Step RV.Delegation.special5Next
      c.mode.val c.iteration.val c.round.val n.1 n.2.1 n.2.2 (by omega) column
      (by simp only [ControlState.packed] at *; omega) mode (by rw [hn]) pointer
      ⟨pointerAligned, by simp only [RV.RAM_END]; omega⟩ S.mem
  have alignedWrites : ∀ aw ∈ RV.writesAt pointer (RV.laneWords L), aw.1.toNat % 4 = 0 := by
    intro aw member
    exact (RV.writesAt_in pointer _ (by omega) (by simp only [RV.RAM_END]; omega) aw member).1
  have nextValue : RV.Delegation.control n.1 n.2.1 n.2.2 =
      BitVec.ofNat 32 (scheduleControl ⟨call.val + 1, by omega⟩).packed := by
    simp only [RV.Delegation.control]
    rw [nextEq, schedNext]
  have lane (l : Fin 31) : L[l].toNat =
      (RV.read T.mem (pointer + BitVec.ofNat 32 (8 * l.val)) 4).toNat +
        2 ^ 32 * (RV.read T.mem (pointer + BitVec.ofNat 32 (8 * l.val) + 4) 4).toNat := by
    rw [stepNat l]
    have reads : (fun j : Fin 31 => (RV.readLanes S.mem pointer 31)[j].toNat) = rvPhysicalLanes S pointer := by
      funext j
      exact (rv_physical_lanes_read S pointer j).symm
    rw [reads, ← physical, rv_physical_lanes_read, read_lane_toNat]
  obtain ⟨U, call', same⟩ := call_same (S := S.setPC x) (T := T) effect alignedWrites rom input
    (by
      intro r
      by_cases r10 : r = 10
      · subst r10
        simp only [true_and, show (10 : BitVec 5) ≠ 0 by decide, ne_eq, not_false_eq_true, ite_true]
        exact x10'.trans nextValue.symm
      · simp only [r10, false_and, ite_false]
        exact regs r r10)
    (by
      intro a alignedA
      rw [storeAll_setPC]
      change RV.read T.mem a 4 = RV.read (S.storeAll (RV.writesAt pointer (RV.laneWords L))).mem a 4
      by_cases inside : ∃ j : Fin 62, a = pointer + BitVec.ofNat 32 (4 * j.val)
      · obtain ⟨j, rfl⟩ := inside
        have spec := read_writesAt_at S [] [] pointer (RV.laneWords L) fits (by simp) j
        simp only [List.nil_append, List.append_nil] at spec
        rw [spec]
        have l2 : j.val / 2 < 31 := by omega
        obtain ⟨lowHalf, highHalf⟩ := lane_halves L[j.val / 2]
          (RV.read T.mem (pointer + BitVec.ofNat 32 (8 * (j.val / 2))) 4)
          (RV.read T.mem (pointer + BitVec.ofNat 32 (8 * (j.val / 2)) + 4) 4) (lane ⟨j.val / 2, l2⟩)
        have entry : (RV.laneWords L)[j] = L[j.val / 2].extractLsb' (32 * (j.val % 2)) 32 := by
          simp only [RV.laneWords, Fin.getElem_fin, Vector.getElem_ofFn]
        rw [entry]
        rcases Nat.mod_two_eq_zero_or_one j.val with even | odd
        · rw [even, Nat.mul_zero, lowHalf, show 4 * j.val = 8 * (j.val / 2) by omega]
        · rw [odd, Nat.mul_one, highHalf, show 4 * j.val = 8 * (j.val / 2) + 4 by omega, BitVec.ofNat_add,
            ← BitVec.add_assoc]
          rfl
      · have outside : ∀ j : Fin 62, a ≠ pointer + BitVec.ofNat 32 (4 * j.val) :=
          fun j same => inside ⟨j, same⟩
        rw [words a alignedA outside, RV.read_storeAll_other S _ a (by have := a.isLt; omega)
          (writesAt_disjoint pointer a _ (by omega) fits alignedA outside)])
  exact ⟨U, call', same⟩

end Airbender.Keccak.Proofs
