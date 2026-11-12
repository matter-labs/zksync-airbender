module
public import Proven.KeccakSplit.ColumnParity.Ports

@[expose] public section

/- The column-parity worker's row contract, but `executes`: canonical writes, the call
   effect, x11 alignment and the lane addresses (ported from PR #585's
   parity_write_words_bounded, parity_native_reference_schedule, parity_call_lane_address). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

abbrev parityRow (w : Nat → ZMod babyBearModulus) : Native.Row babyBearModulus := ⟨.columnParity, w⟩

theorem pointer_aligned_word (w : Nat → ZMod babyBearModulus) (h : Holds w) :
    ((parityRow w).readWord 1).value % 256 = 0 := by
  rw [read_word_pointer]
  have := pointer_aligned h
  simp only [Word.value, limbBase]
  omega

theorem write_col_lane (k : Nat) (k2 : 2 ≤ k) (k14 : k < 14) :
    writeCol k = limbColumn true ⟨(k - 2) / 2, by omega⟩ ⟨2 * ((k - 2) % 2), by omega⟩ ∧
      writeCol k + 1 = limbColumn true ⟨(k - 2) / 2, by omega⟩ ⟨2 * ((k - 2) % 2) + 1, by omega⟩ := by
  have e1 : 2 + 2 * ((k - 2) / 2) + 2 * ((k - 2) % 2) / 2 = k := by omega
  have e2 : 2 + 2 * ((k - 2) / 2) + (2 * ((k - 2) % 2) + 1) / 2 = k := by omega
  have e3 : 2 * ((k - 2) % 2) % 2 = 0 := by omega
  have e4 : (2 * ((k - 2) % 2) + 1) % 2 = 1 := by omega
  show writeCol k = writeCol (2 + 2 * ((k - 2) / 2) + 2 * ((k - 2) % 2) / 2) + 2 * ((k - 2) % 2) % 2 ∧
    writeCol k + 1 = writeCol (2 + 2 * ((k - 2) / 2) + (2 * ((k - 2) % 2) + 1) / 2) +
      (2 * ((k - 2) % 2) + 1) % 2
  rw [e1, e2, e3, e4, Nat.add_zero]
  exact ⟨rfl, rfl⟩

theorem writes (w : Nat → ZMod babyBearModulus) (h : Holds w) (active : w 0 = 1)
    (reads : ∀ p ∈ (parityRow w).ports, (readToken w p).word.Bounded) :
    ∀ p ∈ (parityRow w).ports, ((parityRow w).writeToken p).word.Bounded := by
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
  by_cases readonly : k.val = 1 ∨ (4 ≤ k.val ∧ k.val < 12)
  · have same : writeCol k = readCol k := by
      simp only [writeCol, readCol]; split_ifs <;> omega
    have r := reads _ (port_member w k)
    rw [read_token_word] at r
    rw [same]
    exact r
  · obtain ⟨c0, c1⟩ := write_col_lane k.val (by omega) k.isLt
    rw [c1, c0]
    exact ⟨(write_limb_value h _ _).1, (write_limb_value h _ _).1⟩

theorem read_lanes (w : Nat → ZMod babyBearModulus) : (parityRow w).readLanes = refLanes w false := by
  apply Vector.ext
  intro l bound
  simp only [Native.Row.readLanes, refLanes, Vector.getElem_ofFn]
  by_cases live : l < 6
  · have slot : l < Call.slotCount (parityRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]
    have lo := read_word_lane w l live false
    have hi := read_word_lane w l live true
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
    rw [show 3 + 2 * l = 2 + 2 * l + 1 by omega, lo, hi]
    simp only [Word.value, limbBase, laneValue, packFourChunks]
    ring
  · have slot : ¬ l < Call.slotCount (parityRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]

theorem written_lanes (w : Nat → ZMod babyBearModulus) :
    (parityRow w).writtenLanes = refLanes w true := by
  apply Vector.ext
  intro l bound
  simp only [Native.Row.writtenLanes, refLanes, Vector.getElem_ofFn]
  by_cases live : l < 6
  · have slot : l < Call.slotCount (parityRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]
    have lo := written_word_lane w l live false
    have hi := written_word_lane w l live true
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
    rw [show 3 + 2 * l = 2 + 2 * l + 1 by omega, lo, hi]
    simp only [Word.value, limbBase, laneValue, packFourChunks]
    ring
  · have slot : ¬ l < Call.slotCount (parityRow w).kind := live
    simp only [slot, live, ↓reduceIte, ↓reduceDIte]

theorem effects (w : Nat → ZMod babyBearModulus) (h : Holds w) (active : w 0 = 1) :
    Native.RowEffects (parityRow w) := by
  obtain ⟨index, kind, control, next, round, _⟩ := controller h active
  have high := control_high h
  have selected : (row w 1)[3] = ((selectedRound index).val : ZMod babyBearModulus) := by
    rw [(control_entries w).2.2.2, round]
    rfl
  refine ⟨index, kind, ?_, ?_, ?_⟩
  · rw [read_word_control, control, high.1, control_val, ZMod.val_zero]
  · rw [written_word_control, next, high.2, bump_val, ZMod.val_zero]
  · rw [read_lanes, written_lanes]
    exact reference_result h index kind selected

theorem addresses (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (control : (parityRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (pointerBound : ((parityRow w).readWord 1).Bounded) :
    ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt index.val) → ∀ high : Bool,
      ∃ p ∈ (parityRow w).ports, p.address.code w =
        (Call.laneCell ((parityRow w).readWord 1).toBitVec (Call.slots index)[lane] high).addressCode := by
  obtain ⟨actual, kind, c3, _, _, slots⟩ := controller h active
  have same : actual = index := by
    have low := congrArg Word.lo control
    rw [read_word_control] at low
    dsimp only at low
    rw [c3, control_val] at low
    exact Fin.ext (SetupProofs.controlAt_inj actual.isLt index.isLt low)
  subst same
  intro lane live high
  rw [kind] at live
  change lane.val < 6 at live
  refine ⟨port (lanePort ⟨lane.val, live⟩ high), port_member w _, ?_⟩
  rw [lane_address, slots ⟨lane.val, live⟩]
  rw [read_word_pointer] at pointerBound ⊢
  exact lane_address_code high pointerBound.1 pointerBound.2 (pointer_aligned h)

end Airbender.Keccak.Split.ColumnParity.Proofs
