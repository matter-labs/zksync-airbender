module
public import Slop.KeccakSplit.ThetaRho.Ports

@[expose] public section

/- The theta/rho worker's row contract, but `executes`: canonical writes, the call
   effect, x11 alignment and the lane addresses (ported from PR #585's
   theta_write_words_bounded, theta_native_reference_schedule, theta_call_lane_address). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

abbrev thetaRow (w : Nat → ZMod babyBearModulus) : Native.Row babyBearModulus := ⟨.thetaRho, w⟩

theorem pointer_aligned_word (w : Nat → ZMod babyBearModulus) (h : Holds w) :
    ((thetaRow w).readWord 1).value % 256 = 0 := by
  rw [read_word_pointer]
  have := pointer_aligned h
  simp only [Word.value, limbBase]
  omega

theorem write_col_lane (k : Nat) (k2 : 2 ≤ k) (k16 : k < 16) :
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
    (reads : ∀ p ∈ (thetaRow w).ports, (readToken w p).word.Bounded) :
    ∀ p ∈ (thetaRow w).ports, ((thetaRow w).writeToken p).word.Bounded := by
  intro p member
  obtain ⟨k, rfl⟩ := member_port member
  rw [write_token_word]
  obtain ⟨index, _, _, next, flags, _⟩ := controller h active
  by_cases k0 : k.val = 0
  · have e : k = 0 := Fin.ext k0
    subst e
    show (w 5).val < limbBase ∧ (w 6).val < limbBase
    rw [next, bump_val, (control_high h).2, ZMod.val_zero]
    exact ⟨bump_small (SetupProofs.controlAt_lt index.isLt), by decide⟩
  by_cases readonly : k.val = 1 ∨ 12 ≤ k.val
  · have same : writeCol k = readCol k := by
      simp only [writeCol, readCol]; split_ifs <;> omega
    have r := reads _ (port_member w k)
    rw [read_token_word] at r
    rw [same]
    exact r
  · obtain ⟨c0, c1⟩ := write_col_lane k.val (by omega) k.isLt
    rw [c1, c0]
    let column : Fin 5 := ⟨index.val % 5, Nat.mod_lt _ (by decide)⟩
    let lane : Fin 5 := ⟨(k.val - 2) / 2, by omega⟩
    exact ⟨(write_limb_value h column lane _ flags).1, (write_limb_value h column lane _ flags).1⟩

theorem lanes_eq (w : Nat → ZMod babyBearModulus) (writing : Bool) :
    (if writing then (thetaRow w).writtenLanes else (thetaRow w).readLanes) = refLanes w writing := by
  apply Vector.ext
  intro l bound
  cases writing
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, Native.Row.readLanes, Native.Row.writtenLanes,
      refLanes, Vector.getElem_ofFn]
    have slot : l < Call.slotCount (thetaRow w).kind := bound
    simp only [slot, ↓reduceIte]
    rw [show 3 + 2 * l = 2 + 2 * l + 1 by omega]
  · have lo := read_word_lane w l bound false
    have hi := read_word_lane w l bound true
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
    rw [lo, hi]
    simp only [Word.value, limbBase, laneValue, packLane, Vector.getElem_ofFn, Fin.reduceFinMk, Fin.isValue]
    ring
  · have lo := written_word_lane w l bound false
    have hi := written_word_lane w l bound true
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at lo hi
    rw [lo, hi]
    simp only [Word.value, limbBase, laneValue, packLane, Vector.getElem_ofFn, Fin.reduceFinMk, Fin.isValue]
    ring

theorem effects (w : Nat → ZMod babyBearModulus) (h : Holds w) (active : w 0 = 1)
    (reads : ∀ p ∈ (thetaRow w).ports, (readToken w p).word.Bounded) :
    Native.RowEffects (thetaRow w) := by
  obtain ⟨index, kind, control, next, flags, _⟩ := controller h active
  have high := control_high h
  have bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536 := by
    have r14 := reads _ (port_member w 14)
    have r15 := reads _ (port_member w 15)
    rw [read_token_word] at r14 r15
    intro limb
    fin_cases limb
    exacts [r14.1, r14.2, r15.1, r15.2]
  refine ⟨index, kind, ?_, ?_, ?_⟩
  · rw [read_word_control, control, high.1, control_val, ZMod.val_zero]
  · rw [written_word_control, next, high.2, bump_val, ZMod.val_zero]
  · have r := lanes_eq w false
    have t := lanes_eq w true
    simp only [Bool.false_eq_true, ↓reduceIte] at r t
    rw [r, t]
    exact reference_result h index kind flags bounds

theorem addresses (w : Nat → ZMod babyBearModulus) (index : Fin 361) (h : Holds w)
    (active : w 0 = 1) (control : (thetaRow w).readWord 0 = ⟨controlAt index.val, 0⟩)
    (pointerBound : ((thetaRow w).readWord 1).Bounded) :
    ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt index.val) → ∀ high : Bool,
      ∃ p ∈ (thetaRow w).ports, p.address.code w =
        (Call.laneCell ((thetaRow w).readWord 1).toBitVec (Call.slots index)[lane] high).addressCode := by
  obtain ⟨actual, kind, c3, _, _, slots⟩ := controller h active
  have same : actual = index := by
    have low := congrArg Word.lo control
    rw [read_word_control] at low
    dsimp only at low
    rw [c3, control_val] at low
    exact Fin.ext (SetupProofs.controlAt_inj actual.isLt index.isLt low)
  subst same
  intro lane _ high
  refine ⟨port (lanePort lane high), port_member w _, ?_⟩
  rw [lane_address, slots lane]
  rw [read_word_pointer] at pointerBound ⊢
  exact lane_address_code high pointerBound.1 pointerBound.2 (pointer_aligned h)

end Airbender.Keccak.Split.ThetaRho.Proofs
