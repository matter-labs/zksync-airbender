import Slop.KeccakSplit.ColumnParity.Fields
import Slop.KeccakSplit.RowExecution

/- The column-parity row executes its call in Sail (ported from PR #585's lane-halves,
   write-projection and call-execution modules). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Trace.Proofs Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
  Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem read_word_port (w : Nat → ZMod babyBearModulus) (k : Fin 14) :
    (parityRow w).readWord k.val = (readToken w (port k)).word := by
  simp only [Native.Row.readWord, port_get w k k.isLt]

theorem written_word_port (w : Nat → ZMod babyBearModulus) (k : Fin 14) :
    (parityRow w).writtenWord k.val = ((parityRow w).writeToken (port k)).word := by
  simp only [Native.Row.writtenWord, port_get w k k.isLt]

theorem ports_enumeration (w : Nat → ZMod babyBearModulus) :
    (parityRow w).ports.toList = [port 0, port 1] ++
      (List.finRange 6).flatMap (fun lane => [port (lanePort lane false), port (lanePort lane true)]) := by
  rfl

/-- The lane ports address the call's slots relative to the x11 pointer. -/
theorem lane_port_address (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (control : (parityRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (pointerBound : ((parityRow w).readWord 1).Bounded) (lane : Fin 6) (high : Bool) :
    (port (lanePort lane high)).address.code w =
      (Call.laneCell ((parityRow w).readWord 1).toBitVec (Call.slots index)[lane.val] high).addressCode := by
  obtain ⟨actual, _, c3, _, _, slots⟩ := controller h active
  have same : actual = index := by
    have low := congrArg Word.lo control
    rw [read_word_control] at low
    dsimp only at low
    rw [c3, control_val] at low
    exact Fin.ext (SetupProofs.controlAt_inj actual.isLt index.isLt low)
  subst same
  rw [lane_address, slots lane]
  rw [read_word_pointer] at pointerBound ⊢
  exact lane_address_code high pointerBound.1 pointerBound.2 (pointer_aligned h)

/-- A written lane half is the matching half of the written lane value. -/
theorem lane_port_value (w : Nat → ZMod babyBearModulus)
    (bounded : ∀ k : Fin 14, ((parityRow w).writeToken (port k)).word.Bounded) (lane : Fin 6) (high : Bool) :
    memoryWord ((port (lanePort lane high)).writeCode w) =
      Call.half (parityRow w).writtenLanes[lane.val] high := by
  have value : (parityRow w).writtenLanes[lane.val] =
      ((parityRow w).writtenWord (2 + 2 * lane.val)).value +
        2 ^ 32 * ((parityRow w).writtenWord (3 + 2 * lane.val)).value := by
    have live : lane.val < Call.slotCount (parityRow w).kind := lane.isLt
    simp only [Native.Row.writtenLanes, Vector.getElem_ofFn, live, ↓reduceIte]
  have lo := written_word_port w (lanePort lane false)
  have hi := written_word_port w (lanePort lane true)
  simp only [lanePort, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
  rw [show 3 + 2 * lane.val = 2 + 2 * lane.val + 1 by omega] at value
  rw [value, lo, hi, half_words (bounded _) (bounded _)]
  cases high <;> rfl

theorem write_projection (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (kind : kindAt index.val = .columnParity)
    (control : (parityRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (next : (parityRow w).writtenWord 0 = ⟨bump (controlAt index.val), 0⟩)
    (pointerBound : ((parityRow w).readWord 1).Bounded)
    (bounded : ∀ k : Fin 14, ((parityRow w).writeToken (port k)).word.Bounded) :
    ((parityRow w).memorySteps.map transferEvent).map (fun event => (event.2.1, memoryWord event.2.2.2)) =
      (Call.writes index ((parityRow w).readWord 1).toBitVec (parityRow w).writtenLanes).map
        (fun entry => (entry.1.addressCode, entry.2)) := by
  simp only [Native.Row.memorySteps, List.map_map, Function.comp_def, transferEvent]
  rw [ports_enumeration]
  have controlAddress : (readToken w (port 0)).address = (Cell.register 10).addressCode := rfl
  have pointerAddress : (readToken w (port 1)).address = (Cell.register 11).addressCode := rfl
  have controlWord : memoryWord ((parityRow w).writeToken (port 0)).value =
      BitVec.ofNat 32 (bump (controlAt index.val)) := by
    have e := written_word_port w 0
    change (parityRow w).writtenWord 0 = _ at e
    rw [next] at e
    change (((parityRow w).writeToken (port 0)).word).toBitVec = _
    rw [← e]
    simp [Word.toBitVec, Word.value]
  have pointerWord : memoryWord ((parityRow w).writeToken (port 1)).value =
      ((parityRow w).readWord 1).toBitVec := by
    have e := read_word_port w 1
    change (parityRow w).readWord 1 = _ at e
    change (readToken w (port 1)).word.toBitVec = _
    rw [← e]
  have address (lane : Fin 6) (high : Bool) : (readToken w (port (lanePort lane high))).address =
      (Call.laneCell ((parityRow w).readWord 1).toBitVec (Call.slots index)[lane.val] high).addressCode :=
    lane_port_address w index h active control pointerBound lane high
  have value (lane : Fin 6) (high : Bool) :
      memoryWord ((parityRow w).writeToken (port (lanePort lane high))).value =
        Call.half (parityRow w).writtenLanes[lane.val] high :=
    lane_port_value w bounded lane high
  have finList : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  have rangeList : List.range 6 = [0, 1, 2, 3, 4, 5] := by decide
  simp only [Call.writes, kind, Call.slotCount, finList, rangeList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_cons, List.map_nil, Nat.reduceLT, ↓reduceDIte,
    controlAddress, pointerAddress, controlWord, pointerWord, address, value]
  rfl

theorem executes (w : Nat → ZMod babyBearModulus) (index : Fin 361) {before after : State}
    {cells : List Cell} {events : List MemoryAccess} (h : Holds w) (active : w 0 = 1)
    (arguments : Call.ArgumentsAt index.val before)
    (reads : ∀ p ∈ (parityRow w).ports, (readToken w p).word.Bounded)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((parityRow w).memorySteps.map transferEvent))
    (observed : ∀ p ∈ (parityRow w).ports, ∃ cell : Cell, cell.addressCode = p.address.code w ∧
      cell.read before = .ok (readToken w p).word.toBitVec before) :
    Call.ExecutesAt index before after := by
  obtain ⟨actual, kind, control, next, result⟩ := effects w h active
  have controlRead := observed_read (target := .register 10) rfl (observed _ (port_member w 0))
  rw [← read_word_port w 0, show ((0 : Fin 14) : Nat) = 0 from rfl, control] at controlRead
  have same := control_index arguments controlRead
  subst same
  have pointerRead := observed_read (target := .register 11) rfl (observed _ (port_member w 1))
  rw [← read_word_port w 1, show ((1 : Fin 14) : Nat) = 1 from rfl] at pointerRead
  have pointerBound : ((parityRow w).readWord 1).Bounded := by
    rw [show (1 : Nat) = ((1 : Fin 14) : Nat) from rfl, read_word_port]
    exact reads _ (port_member w 1)
  have bounded (k : Fin 14) : ((parityRow w).writeToken (port k)).word.Bounded :=
    writes w h active reads _ (port_member w k)
  have readBound (k : Fin 14) : ((parityRow w).readWord k.val).Bounded := by
    rw [read_word_port]; exact reads _ (port_member w k)
  have lanes : ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt actual.val) →
      (parityRow w).readLanes[lane] < 2 ^ 64 ∧
      (Call.laneCell ((parityRow w).readWord 1).toBitVec (Call.slots actual)[lane] false).read before =
        .ok (Call.half (parityRow w).readLanes[lane] false) before ∧
      (Call.laneCell ((parityRow w).readWord 1).toBitVec (Call.slots actual)[lane] true).read before =
        .ok (Call.half (parityRow w).readLanes[lane] true) before := by
    intro lane live
    rw [kind] at live
    change lane.val < 6 at live
    let l : Fin 6 := ⟨lane.val, live⟩
    have value : (parityRow w).readLanes[lane] =
        ((parityRow w).readWord (2 + 2 * lane.val)).value +
          2 ^ 32 * ((parityRow w).readWord (2 + 2 * lane.val + 1)).value := by
      have slot : lane.val < Call.slotCount (parityRow w).kind := live
      simp only [Native.Row.readLanes, Fin.getElem_fin, Vector.getElem_ofFn, slot, ↓reduceIte]
      rw [show 3 + 2 * lane.val = 2 + 2 * lane.val + 1 by omega]
    have b0 := readBound (lanePort l false)
    have b1 := readBound (lanePort l true)
    simp only [lanePort, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at b0 b1
    have read (high : Bool) := observed_read
      (lane_port_address w actual h active control pointerBound l high) (observed _ (port_member w _))
    have w0 : (readToken w (port (lanePort l false))).word = (parityRow w).readWord (2 + 2 * lane.val) := by
      rw [← read_word_port]; rfl
    have w1 : (readToken w (port (lanePort l true))).word =
        (parityRow w).readWord (2 + 2 * lane.val + 1) := by
      rw [← read_word_port]; rfl
    have r0 := read false
    have r1 := read true
    rw [w0] at r0
    rw [w1] at r1
    refine ⟨?_, ?_, ?_⟩
    · rw [value]; exact lane_words_bound b0 b1
    · rw [value, half_words b0 b1]; exact r0
    · rw [value, half_words b0 b1]; exact r1
  exact executes_of_projection (parityRow w) actual arguments _ pointerRead (parityRow w).readLanes lanes
    history permutation (by
      rw [result]
      exact write_projection w actual h active kind control next pointerBound bounded)

end Airbender.Keccak.Split.ColumnParity.Proofs
