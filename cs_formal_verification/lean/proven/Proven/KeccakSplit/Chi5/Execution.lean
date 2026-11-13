module
public import Proven.KeccakSplit.Chi5.Fields
public import Proven.KeccakSplit.RowExecution

@[expose] public section

/- The chi5 row executes its call in Sail (ported from PR #585's SplitChiLaneHalves,
   SplitChiWriteProjection and SplitChiCallExecution). -/

namespace Airbender.Keccak.Split.Chi5.Proofs
open Airbender.Trace Airbender.Trace.Proofs Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

theorem read_word_port (w : Nat → ZMod babyBearModulus) (k : Fin 12) :
    (chiRow w).readWord k.val = (readToken w (port k)).word := by
  simp only [Native.Row.readWord, port_get w k k.isLt]

theorem written_word_port (w : Nat → ZMod babyBearModulus) (k : Fin 12) :
    (chiRow w).writtenWord k.val = ((chiRow w).writeToken (port k)).word := by
  simp only [Native.Row.writtenWord, port_get w k k.isLt]

theorem ports_enumeration (w : Nat → ZMod babyBearModulus) :
    (chiRow w).ports.toList = [port 0, port 1] ++
      (List.finRange 5).flatMap (fun lane => [port (lanePort lane false), port (lanePort lane true)]) := by
  rfl

/-- The lane ports address the call's slots relative to the x11 pointer. -/
theorem lane_port_address (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (control : (chiRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (pointerBound : ((chiRow w).readWord 1).Bounded) (lane : Fin 5) (high : Bool) :
    (port (lanePort lane high)).address.code w =
      (Call.laneCell ((chiRow w).readWord 1).toBitVec (Call.slots index)[lane.val] high).addressCode := by
  obtain ⟨actual, _, c3, _, slots⟩ := controller h active
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
    (bounded : ∀ k : Fin 12, ((chiRow w).writeToken (port k)).word.Bounded) (lane : Fin 5) (high : Bool) :
    memoryWord ((port (lanePort lane high)).writeCode w) =
      Call.half (chiRow w).writtenLanes[lane.val] high := by
  have value : (chiRow w).writtenLanes[lane.val] =
      ((chiRow w).writtenWord (2 + 2 * lane.val)).value +
        2 ^ 32 * ((chiRow w).writtenWord (3 + 2 * lane.val)).value := by
    have live : lane.val < Call.slotCount (chiRow w).kind := lane.isLt
    simp only [Native.Row.writtenLanes, Vector.getElem_ofFn, live, ↓reduceIte]
  have lo := written_word_port w (lanePort lane false)
  have hi := written_word_port w (lanePort lane true)
  simp only [lanePort, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
  rw [show 3 + 2 * lane.val = 2 + 2 * lane.val + 1 by omega] at value
  rw [value, lo, hi, half_words (bounded _) (bounded _)]
  cases high <;> rfl

theorem write_projection (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (kind : kindAt index.val = .chi5)
    (control : (chiRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (next : (chiRow w).writtenWord 0 = ⟨bump (controlAt index.val), 0⟩)
    (pointerBound : ((chiRow w).readWord 1).Bounded)
    (bounded : ∀ k : Fin 12, ((chiRow w).writeToken (port k)).word.Bounded) :
    ((chiRow w).memorySteps.map transferEvent).map (fun event => (event.2.1, memoryWord event.2.2.2)) =
      (Call.writes index ((chiRow w).readWord 1).toBitVec (chiRow w).writtenLanes).map
        (fun entry => (entry.1.addressCode, entry.2)) := by
  simp only [Native.Row.memorySteps, List.map_map, Function.comp_def, transferEvent]
  rw [ports_enumeration]
  have controlAddress : (readToken w (port 0)).address = (Cell.register 10).addressCode := by rfl
  have pointerAddress : (readToken w (port 1)).address = (Cell.register 11).addressCode := by rfl
  have controlWord : memoryWord ((chiRow w).writeToken (port 0)).value =
      BitVec.ofNat 32 (bump (controlAt index.val)) := by
    have e := written_word_port w 0
    change (chiRow w).writtenWord 0 = _ at e
    rw [next] at e
    change (((chiRow w).writeToken (port 0)).word).toBitVec = _
    rw [← e]
    simp [Word.toBitVec, Word.value]
  have pointerWord : memoryWord ((chiRow w).writeToken (port 1)).value =
      ((chiRow w).readWord 1).toBitVec := by
    have e := read_word_port w 1
    change (chiRow w).readWord 1 = _ at e
    change (readToken w (port 1)).word.toBitVec = _
    rw [← e]
  have address (lane : Fin 5) (high : Bool) : (readToken w (port (lanePort lane high))).address =
      (Call.laneCell ((chiRow w).readWord 1).toBitVec (Call.slots index)[lane.val] high).addressCode :=
    lane_port_address w index h active control pointerBound lane high
  have value (lane : Fin 5) (high : Bool) :
      memoryWord ((chiRow w).writeToken (port (lanePort lane high))).value =
        Call.half (chiRow w).writtenLanes[lane.val] high :=
    lane_port_value w bounded lane high
  have finList : List.finRange 5 = [0, 1, 2, 3, 4] := by decide
  have rangeList : List.range 5 = [0, 1, 2, 3, 4] := by decide
  simp only [Call.writes, kind, Call.slotCount, finList, rangeList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_cons, List.map_nil, Nat.reduceLT, ↓reduceDIte,
    controlAddress, pointerAddress, controlWord, pointerWord, address, value]
  rfl

end Airbender.Keccak.Split.Chi5.Proofs
