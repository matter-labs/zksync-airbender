import Slop.KeccakSplit.Chi5.Execution
import Slop.KeccakSplit.RVRowExecution

/-! RV twin of `Chi5/Execution.lean`'s `executes`: the row executes its call on `RV.State`s (RAM cells include the
    shadow RAM below `ROM_END`). -/

namespace Airbender.Keccak.Split.Chi5.Proofs
open Airbender.Trace Airbender.Trace.Proofs Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

theorem rv_executes (w : Nat → ZMod babyBearModulus) (index : Fin 361) {before after : RV.State}
    {cells : List Cell} {events : List MemoryAccess} (h : Holds w) (active : w 0 = 1)
    (arguments : Call.RVArgumentsAt index.val before)
    (reads : ∀ p ∈ (chiRow w).ports, (readToken w p).word.Bounded)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((chiRow w).memorySteps.map transferEvent))
    (observed : ∀ p ∈ (chiRow w).ports, ∃ cell : Cell, cell.addressCode = p.address.code w ∧
      cell.readRV before = some (readToken w p).word.toBitVec) :
    Call.RVExecutesAt index before after := by
  obtain ⟨actual, kind, control, next, result⟩ := effects w h active
  have controlRead := rv_observed_read (target := .register 10) rfl (observed _ (port_member w 0))
  rw [← read_word_port w 0, show ((0 : Fin 12) : Nat) = 0 from rfl, control] at controlRead
  have same := rv_control_index arguments controlRead
  subst same
  have pointerRead := rv_observed_read (target := .register 11) rfl (observed _ (port_member w 1))
  rw [← read_word_port w 1, show ((1 : Fin 12) : Nat) = 1 from rfl] at pointerRead
  have pointerBound : ((chiRow w).readWord 1).Bounded := by
    rw [show (1 : Nat) = ((1 : Fin 12) : Nat) from rfl, read_word_port]
    exact reads _ (port_member w 1)
  have bounded (k : Fin 12) : ((chiRow w).writeToken (port k)).word.Bounded :=
    writes w h active reads _ (port_member w k)
  have readBound (k : Fin 12) : ((chiRow w).readWord k.val).Bounded := by
    rw [read_word_port]; exact reads _ (port_member w k)
  have lanes : ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt actual.val) →
      (chiRow w).readLanes[lane] < 2 ^ 64 ∧
      (Call.laneCell ((chiRow w).readWord 1).toBitVec (Call.slots actual)[lane] false).readRV before =
        some (Call.half (chiRow w).readLanes[lane] false) ∧
      (Call.laneCell ((chiRow w).readWord 1).toBitVec (Call.slots actual)[lane] true).readRV before =
        some (Call.half (chiRow w).readLanes[lane] true) := by
    intro lane live
    rw [kind] at live
    change lane.val < 5 at live
    let l : Fin 5 := ⟨lane.val, live⟩
    have value : (chiRow w).readLanes[lane] =
        ((chiRow w).readWord (2 + 2 * lane.val)).value +
          2 ^ 32 * ((chiRow w).readWord (2 + 2 * lane.val + 1)).value := by
      have slot : lane.val < Call.slotCount (chiRow w).kind := live
      simp only [Native.Row.readLanes, Fin.getElem_fin, Vector.getElem_ofFn, slot, ↓reduceIte]
      rw [show 3 + 2 * lane.val = 2 + 2 * lane.val + 1 by omega]
    have b0 := readBound (lanePort l false)
    have b1 := readBound (lanePort l true)
    simp only [lanePort, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at b0 b1
    have read (high : Bool) := rv_observed_read
      (lane_port_address w actual h active control pointerBound l high) (observed _ (port_member w _))
    have w0 : (readToken w (port (lanePort l false))).word = (chiRow w).readWord (2 + 2 * lane.val) := by
      rw [← read_word_port]; rfl
    have w1 : (readToken w (port (lanePort l true))).word =
        (chiRow w).readWord (2 + 2 * lane.val + 1) := by
      rw [← read_word_port]; rfl
    have r0 := read false
    have r1 := read true
    rw [w0] at r0
    rw [w1] at r1
    refine ⟨?_, ?_, ?_⟩
    · rw [value]; exact lane_words_bound b0 b1
    · rw [value, half_words b0 b1]; exact r0
    · rw [value, half_words b0 b1]; exact r1
  exact rv_executes_of_projection (chiRow w) actual arguments _ pointerRead (chiRow w).readLanes lanes
    history permutation (by
      rw [result]
      exact write_projection w actual h active kind control next pointerBound bounded)

end Airbender.Keccak.Split.Chi5.Proofs
