module
public import Slop.KeccakSplit.Chi5.Ports
public import Slop.KeccakSplit.Setup.Facts

@[expose] public section

/- The chi5 worker's row contract, but `executes`: canonical writes, the call
   effect, x11 alignment and the lane addresses (ported from PR #585's
   chi5_write_words_bounded, chi5_native_memory_effect, chi5_native_reference_result,
   chi5_call_lane_address). -/

namespace Airbender.Keccak.Split.Chi5.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

abbrev chiRow (w : Nat → ZMod babyBearModulus) : Native.Row babyBearModulus := ⟨.chi5, w⟩

theorem pointer_aligned_word (w : Nat → ZMod babyBearModulus) (h : Holds w) :
    ((chiRow w).readWord 1).value % 256 = 0 := by
  rw [read_word_pointer]
  have := pointer_aligned h
  simp only [Word.value, limbBase]
  omega

theorem writes (w : Nat → ZMod babyBearModulus) (h : Holds w) (active : w 0 = 1)
    (reads : ∀ p ∈ (chiRow w).ports, (readToken w p).word.Bounded) :
    ∀ p ∈ (chiRow w).ports, ((chiRow w).writeToken p).word.Bounded := by
  intro p member
  obtain ⟨k, rfl⟩ := member_port member
  rw [write_token_word]
  by_cases k0 : k.val = 0
  · obtain ⟨index, _, _, next, _⟩ := controller h active
    have e : k = 0 := Fin.ext k0
    subst e
    show (w 5).val < limbBase ∧ (w 6).val < limbBase
    rw [next, bump_val, (control_high h).2, ZMod.val_zero]
    exact ⟨bump_small (SetupProofs.controlAt_lt index.isLt), by decide⟩
  by_cases k1 : k.val = 1
  · have e : k = 1 := Fin.ext k1
    subst e
    have r := reads _ (port_member w 1)
    rw [read_token_word] at r
    exact r
  · obtain ⟨c0, c1⟩ := write_col_lane k.val (by omega) k.isLt
    rw [c1, c0]
    exact ⟨(limb_value h true _ _).1, (limb_value h true _ _).1⟩

/-- Lane values padded to the seven call positions. -/
def refLanes (w : Nat → ZMod babyBearModulus) (writing : Bool) : Vector Nat 7 :=
  Vector.ofFn fun lane => if active : lane.val < 5 then laneValue w writing ⟨lane.val, active⟩ else 0

theorem read_lanes (w : Nat → ZMod babyBearModulus) : (chiRow w).readLanes = refLanes w false := by
  apply Vector.ext
  intro l bound
  simp only [Native.Row.readLanes, refLanes, Vector.getElem_ofFn]
  by_cases live : l < 5
  · have slot : l < Call.slotCount (chiRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]
    have lo := read_word_lane w l live false
    have hi := read_word_lane w l live true
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
    rw [show 3 + 2 * l = 2 + 2 * l + 1 by omega, lo, hi]
    simp only [Word.value, limbBase, laneValue]
    ring
  · have slot : ¬ l < Call.slotCount (chiRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]

theorem written_lanes (w : Nat → ZMod babyBearModulus) :
    (chiRow w).writtenLanes = refLanes w true := by
  apply Vector.ext
  intro l bound
  simp only [Native.Row.writtenLanes, refLanes, Vector.getElem_ofFn]
  by_cases live : l < 5
  · have slot : l < Call.slotCount (chiRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]
    have lo := written_word_lane w l live false
    have hi := written_word_lane w l live true
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
    rw [show 3 + 2 * l = 2 + 2 * l + 1 by omega, lo, hi]
    simp only [Word.value, limbBase, laneValue]
    ring
  · have slot : ¬ l < Call.slotCount (chiRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]

theorem reference_result (w : Nat → ZMod babyBearModulus) (h : Holds w)
    (index : Fin 361) (kind : kindAt index.val = .chi5) :
    Call.result index (refLanes w false) = refLanes w true := by
  apply Vector.ext
  intro lane bound
  simp only [Call.result, kind, refLanes, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases live : lane < 5
  · have first : (lane + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
    have second : (lane + 2) % 5 < 5 := Nat.mod_lt _ (by decide)
    simp only [live, first, second, ↓reduceDIte]
    exact (lane_operation h ⟨lane, live⟩).symm
  · simp only [live, ↓reduceDIte]

theorem effects (w : Nat → ZMod babyBearModulus) (h : Holds w) (active : w 0 = 1) :
    Native.RowEffects (chiRow w) := by
  obtain ⟨index, kind, control, next, _⟩ := controller h active
  have high := control_high h
  refine ⟨index, kind, ?_, ?_, ?_⟩
  · rw [read_word_control, control, high.1, control_val, ZMod.val_zero]
  · rw [written_word_control, next, high.2, bump_val, ZMod.val_zero]
  · rw [read_lanes, written_lanes]
    exact reference_result w h index kind

theorem addresses (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (control : (chiRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (pointerBound : ((chiRow w).readWord 1).Bounded) :
    ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt index.val) → ∀ high : Bool,
      ∃ p ∈ (chiRow w).ports, p.address.code w =
        (Call.laneCell ((chiRow w).readWord 1).toBitVec (Call.slots index)[lane] high).addressCode := by
  obtain ⟨actual, kind, c3, _, slots⟩ := controller h active
  have same : actual = index := by
    have low := congrArg Word.lo control
    rw [read_word_control] at low
    dsimp only at low
    rw [c3, control_val] at low
    exact Fin.ext (SetupProofs.controlAt_inj actual.isLt index.isLt low)
  subst same
  intro lane live high
  rw [kind] at live
  change lane.val < 5 at live
  refine ⟨port (lanePort ⟨lane.val, live⟩ high), port_member w _, ?_⟩
  rw [lane_address, slots ⟨lane.val, live⟩]
  rw [read_word_pointer] at pointerBound ⊢
  exact lane_address_code high pointerBound.1 pointerBound.2 (pointer_aligned h)

end Airbender.Keccak.Split.Chi5.Proofs
