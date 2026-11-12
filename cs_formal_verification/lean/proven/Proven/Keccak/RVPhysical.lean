module
public import Proven.Keccak.PhysicalStep
public import Proven.Delegation.RVNativeViews
public import Proven.ISA.RV.Attr
public import Proven.Keccak.CallPorts
public import Proven.Trace.RVHistoryFrame
public import Batteries.Data.Fin.Fold
public import Proven.Defs.Circuits.Keccak.Artifact
public import Proven.Defs.Trace.Workers.Keccak.Call

@[expose] public section

/-! RV twins of `StateTransport.lean`, `LaneFrame.lean`, `PhysicalStep.lean` and `CallPhysical.lean`: each special5
    call's RV history touches x10, x11 and the twelve lane halves of its six slots only (`rv_keccak_row_frame`),
    reads and writes its lanes in actual RV RAM (`rv_native_lane_observations`), and so moves the 31 physical lanes
    by `microStep` (`rv_native_physical_step`). RAM cells are RAM at any address, the shadow RAM below `ROM_END`
    included. -/

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- The 64-bit lane of an RV state's RAM at `address` (low word, then high word). -/
def rvRamLane (state : RV.State) (address : BitVec 32) : Nat :=
  (rvRamEncoding state address).value + 2 ^ 32 * (rvRamEncoding state (address + 4)).value

/-- The 31 physical lanes at `pointer`. -/
def rvPhysicalLanes (state : RV.State) (pointer : BitVec 32) : LaneState :=
  fun lane => rvRamLane state (pointer + BitVec.ofNat 32 (8 * lane.val))

def wordPort (index : Fin 12) : MemoryPort :=
  importedConstraintsMemoryPorts[2 + index.val]'(by change 2 + index.val < 14; omega)

private theorem word_port_address (index : Fin 12) :
    (wordPort index).address = .indirect importedConstraintsIndirectPorts[index] := by
  fin_cases index <;> rfl

theorem rv_native_word_observations {p : Nat} {w : Nat → ZMod p} {before after : RV.State}
    (addresses : AddressChecks w)
    (reads : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) (index : Fin 12) :
    let address := (statePointer w).toBitVec + BitVec.ofNat 32
      (8 * (w (7 + index.val / 2)).val + 4 * (index.val % 2))
    (rvRamEncoding before address).value = (readToken w (wordPort index)).word.value ∧
      (rvRamEncoding after address).value =
        ((⟨.keccak, w⟩ : Delegation.Row p).writeToken (wordPort index)).word.value := by
  have member : wordPort index ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (by change 2 + index.val < 14; omega)
  have result := rv_indirect_word_observations (word_port_address index)
    (reads _ member) (writes _ member) (observed _ member)
  rw [addresses.addresses index] at result
  exact ⟨congrArg Word.value result.1, congrArg Word.value result.2⟩

theorem rv_native_lane_observations {p : Nat} {w : Nat → ZMod p} {before after : RV.State}
    (addresses : AddressChecks w)
    (reads : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) (lane : Fin 6) :
    let address := (statePointer w).toBitVec + BitVec.ofNat 32 (8 * (w (7 + lane.val)).val)
    Native.readLane w lane = rvRamLane before address ∧
      Native.writtenLane w lane = rvRamLane after address := by
  have low := rv_native_word_observations addresses reads writes observed ⟨2 * lane.val, by omega⟩
  have high := rv_native_word_observations addresses reads writes observed ⟨2 * lane.val + 1, by omega⟩
  fin_cases lane
  all_goals simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at low high ⊢
  all_goals simp only [BitVec.ofNat_add] at high
  all_goals constructor
  all_goals first
    | simpa [rvRamLane, Nat.reducePow, BitVec.add_assoc, Native.readLane, Delegation.Row.readWord,
        Delegation.Row.ports, wordPort, importedConstraintsMemoryPorts] using
        (congrArg₂ (fun a b : Nat => a + 4294967296 * b) low.1 high.1).symm
    | simpa [rvRamLane, Nat.reducePow, BitVec.add_assoc, Native.writtenLane, Delegation.Row.writtenWord,
        Delegation.Row.ports, wordPort, importedConstraintsMemoryPorts] using
        (congrArg₂ (fun a b : Nat => a + 4294967296 * b) low.2 high.2).symm

/-- Every native special5 port touches x10, x11 or one half of one of the call's six slots. -/
theorem keccak_port_cell {p : Nat} {w : Nat → ZMod p} {pointer : BitVec 32} (call : Fin 649)
    (addresses : AddressChecks w) (mapped : statePointer w = Word.ofBitVec pointer)
    (indices : ∀ lane : Fin 6, (w (7 + lane.val)).val = (slotIndices call)[lane])
    {cell : Cell} (i : Fin 14) (code : cell.addressCode = importedConstraintsMemoryPorts[i.val].address.code w) :
    cell = .register 10 ∨ cell = .register 11 ∨ ∃ lane : Fin 6, ∃ half : Fin 2,
      cell = .ram (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane] + 4 * half.val)) := by
  by_cases small : i.val < 2
  · have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · exact Or.inl (cell_address_injective code)
    · exact Or.inr (Or.inl (cell_address_injective code))
  · let position : Fin 12 := ⟨i.val - 2, by omega⟩
    have index : i.val = 2 + position.val := by dsimp [position]; omega
    have shape : importedConstraintsMemoryPorts[i.val].address =
        .indirect importedConstraintsIndirectPorts[position] := by
      simpa only [index, wordPort] using word_port_address position
    rw [shape] at code
    have same := indirect_cell code
    rw [addresses.addresses position, mapped, Word.ofBitVec_roundtrip] at same
    let lane : Fin 6 := ⟨position.val / 2, by have := position.isLt; omega⟩
    let half : Fin 2 := ⟨position.val % 2, Nat.mod_lt _ (by decide)⟩
    refine Or.inr (Or.inr ⟨lane, half, ?_⟩)
    rw [same, indices lane]

/-- A special5 call's RV history leaves every register but x10/x11 and every RAM word outside the call's twelve lane
    halves unchanged; x11 is rewritten with its own value. -/
theorem rv_keccak_row_frame {p : Nat} {w : Nat → ZMod p} {pointer : BitVec 32} {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess} (call : Fin 649)
    (addresses : AddressChecks w) (mapped : statePointer w = Word.ofBitVec pointer)
    (indices : ∀ lane : Fin 6, (w (7 + lane.val)).val = (slotIndices call)[lane])
    (observed : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .keccak w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (∀ r : BitVec 5, r ≠ 10 → r ≠ 11 → after.getReg r = before.getReg r) ∧
    (∀ a : BitVec 32, a.toNat % 4 = 0 →
      (∀ lane : Fin 6, ∀ half : Fin 2, a ≠ pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane] + 4 * half.val)) →
      RV.read after.mem a 4 = RV.read before.mem a 4) := by
  have touched : ∀ event ∈ events, ∃ cell : Cell, cell.addressCode = event.2.1 ∧
      (cell = .register 10 ∨ cell = .register 11 ∨ ∃ lane : Fin 6, ∃ half : Fin 2,
        cell = .ram (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane] + 4 * half.val))) := by
    intro event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have member : port ∈ importedConstraintsMemoryPorts := by
      simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
    obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨cell, code⟩ := observed port (by simpa only [Delegation.Row.ports] using member)
    refine ⟨cell, code, ?_⟩
    subst equal
    exact keccak_port_cell call addresses mapped indices ⟨i, bound⟩ code
  constructor
  · intro r r10 r11
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.register r).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .register r := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | ⟨lane, half, h⟩
      · exact r10 (Cell.register.inj h)
      · exact r11 (Cell.register.inj h)
      · cases h
    have frame := rv_history_cell_frame history aligned (.register r) trivial untouched (readRV_register r before)
    rw [readRV_register] at frame
    exact Option.some.inj frame
  · intro a alignedA outside
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.ram a).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .ram a := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | ⟨lane, half, h⟩
      · cases h
      · cases h
      · exact outside lane half (Cell.ram.inj h)
    have readable := readable_of_aligned (address := a) alignedA
    have frame := rv_history_cell_frame history aligned (.ram a) alignedA untouched (readRV_ram before readable)
    rw [readRV_ram after readable] at frame
    exact Option.some.inj frame

theorem rv_native_physical_step [Fact p.Prime] {w : Nat → ZMod p}
    {pointer : BitVec 32} {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (call : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨call.val, by omega⟩).packed)
    (mapped : statePointer w = Word.ofBitVec pointer)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .keccak w).memorySteps.map Trace.transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (ports : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w)
    (observed : ∀ lane : Fin 6,
      Native.readLane w lane = rvRamLane before (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane])) ∧
      Native.writtenLane w lane = rvRamLane after (pointer + BitVec.ofNat 32 (8 * (slotIndices call)[lane]))) :
    rvPhysicalLanes after pointer = microStep call (rvPhysicalLanes before pointer) := by
  have reads : Vector.ofFn (Native.readLane w) = portReads call (rvPhysicalLanes before pointer) := by
    apply Vector.ext
    intro lane bound
    simpa only [Vector.getElem_ofFn, portReads, rvPhysicalLanes] using (observed ⟨lane, bound⟩).1
  have roundBound : (scheduleControl ⟨call.val, by omega⟩).round.val < 25 := by
    simp only [scheduleControl]
    have := call.isLt
    omega
  have writes := row_micro_writes effects (scheduleControl ⟨call.val, by omega⟩) roundBound control
  rw [reads] at writes
  have indices := scheduled_lane_indices call effects active control
  obtain ⟨_, memFrame⟩ := rv_keccak_row_frame call effects.addresses mapped indices ports history permutation aligned
  funext physical
  let slot := (slotIndices call).toList.idxOf physical.val
  by_cases present : slot < 6
  · have index : (slotIndices call)[slot] = physical.val := by
      simpa only [Vector.getElem_toList] using
        List.getElem_idxOf (show (slotIndices call).toList.idxOf physical.val < (slotIndices call).toList.length by simpa using present)
    have value := congrArg (fun v : Vector Nat 6 => v[slot]) writes
    simp only [Native.writtenLanes, Vector.getElem_ofFn] at value
    have actual := (observed ⟨slot, present⟩).2
    simp only [Fin.getElem_fin] at actual
    rw [index] at actual
    rw [micro_step_get, dite_eq_left present]
    exact actual.symm.trans (value.trans (micro_value_eq (scheduleControl ⟨call.val, by omega⟩)
      roundBound (fun lane => rvPhysicalLanes before pointer
        ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩) ⟨slot, present⟩))
  · have untouched : ∀ lane : Fin 6, (slotIndices call)[lane] ≠ physical.val := by
      intro lane same
      have member : physical.val ∈ (slotIndices call).toList := by
        rw [← same]
        exact List.getElem_mem _
      have short := List.idxOf_lt_length_of_mem member
      exact present (by simpa only [Vector.length_toList] using short)
    have frame (half : Fin 2) :
        RV.read after.mem (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) 4 =
          RV.read before.mem (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) 4 := by
      apply memFrame _ (aligned _ (tracked physical half))
      intro lane other same
      have distinct := lane_half_address_injective pointer physical
        ⟨(slotIndices call)[lane], Controller.Proofs.rows_bound _ lane⟩ half other same
      exact untouched lane (congrArg Fin.val distinct.1).symm
    rw [micro_step_get, dite_eq_right present]
    have low := frame 0
    have high := frame 1
    simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at low high
    simp only [BitVec.ofNat_add] at high
    rw [← BitVec.add_assoc, show BitVec.ofNat 32 4 = (4 : BitVec 32) from rfl] at high
    simp only [rvPhysicalLanes, rvRamLane, rvRamEncoding, low, high]

end Airbender.Keccak.Proofs
