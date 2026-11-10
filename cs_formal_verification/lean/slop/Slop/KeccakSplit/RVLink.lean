module
public import Slop.KeccakSplit.RVStep
public import Slop.KeccakSplit.Setup.Facts
public import Slop.KeccakSplit.Reference.RVExecutions
public import Slop.Keccak.RVCallSteps

@[expose] public section

/-! The split delegate link: one documented split call executed on `RV.State`s (`Call.RVExecutesAt`) is the spec's
    Keccak-f1600 delegation of its worker (`RV.Delegation.keccakF1600`, CSRs `0x7cd`/`0x7cc`/`0x7ce`) from the
    pre-state, up to the spec's PC advance; the 361 calls are the spec's run `RV.calls RV.f1600Calls`. RAM is RAM at
    any address, the shadow RAM below `ROM_END` included. -/

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Delegation.Proofs Spec RV.Delegation
set_option warningAsError true
set_option maxRecDepth 16384

/-- The 31 lanes at `pointer` of an RV state, as values. -/
def rvLanes (state : RV.State) (pointer : BitVec 32) : LaneState :=
  fun l => (RV.readLanes state.mem pointer 31)[l].toNat

theorem rv_lanes_bound (state : RV.State) (pointer : BitVec 32) (l : Fin 31) : rvLanes state pointer l < 2 ^ 64 :=
  BitVec.isLt _

theorem lane_cell_read (state : RV.State) (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0)
    (l : Fin 31) (high : Bool) :
    (laneCell pointer l high).readRV state = some (half (rvLanes state pointer l) high) := by
  have cellAligned := lane_cell_aligned pointer aligned l high
  rw [laneCell] at cellAligned ⊢
  rw [readRV_ram state (readable_of_aligned cellAligned), rvLanes, Keccak.Proofs.read_lane_toNat, half_combine]
  cases high
  · simp
  · simp only [↓reduceIte]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl

/-- One executed split call moves the 31 lanes by `microStep`. -/
theorem rv_lanes_step {i : Fin 361} {before after : RV.State} {pointer : BitVec 32}
    (execution : RVExecutesAt i before after)
    (read : (Cell.register 11).readRV before = some pointer) :
    rvLanes after pointer = microStep i (rvLanes before pointer) := by
  have aligned := (rv_executes_pointer execution read).1
  obtain ⟨called, input, _, calledRead, reads, atomic⟩ := execution
  have same := Option.some.inj (calledRead.symm.trans read)
  subst same
  have agree (k : Fin 7) (live : k.val < slotCount (kindAt i.val)) :
      input[k] = (Vector.ofFn fun lane : Fin 7 => rvLanes before called (slots i)[lane])[k] := by
    have low := Option.some.inj ((reads k live).2.1.symm.trans (lane_cell_read before called aligned _ false))
    have high := Option.some.inj ((reads k live).2.2.symm.trans (lane_cell_read before called aligned _ true))
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using
      lane_eq_of_halves (reads k live).1 (rv_lanes_bound before called _) low high
  have outputs := result_live_congr i input (Vector.ofFn fun lane : Fin 7 => rvLanes before called (slots i)[lane]) agree
  funext l
  by_cases hit : ∃ k : Fin 7, k.val < slotCount (kindAt i.val) ∧ (slots i)[k] = l
  · obtain ⟨k, live, rfl⟩ := hit
    rw [micro_step_hit i _ k live]
    have sourceBounds (lane : Fin 7) :
        (Vector.ofFn fun lane : Fin 7 => rvLanes before called (slots i)[lane])[lane] < 2 ^ 64 := by
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      exact rv_lanes_bound before called _
    apply lane_eq_of_halves (rv_lanes_bound after called _) (result_lane_bound i _ sourceBounds k)
    · have written := rv_written_lane_reads i called aligned _ atomic k live false
      rw [outputs k live] at written
      exact Option.some.inj ((lane_cell_read after called aligned _ false).symm.trans written)
    · have written := rv_written_lane_reads i called aligned _ atomic k live true
      rw [outputs k live] at written
      exact Option.some.inj ((lane_cell_read after called aligned _ true).symm.trans written)
  · have miss : ∀ k : Fin 7, k.val < slotCount (kindAt i.val) → (slots i)[k] ≠ l :=
      fun k live same => hit ⟨k, live, same⟩
    rw [micro_step_miss i _ l miss]
    apply lane_eq_of_halves (rv_lanes_bound after called _) (rv_lanes_bound before called _)
    · exact Option.some.inj ((lane_cell_read after called aligned _ false).symm.trans
        (rv_unwritten_lane_frame i called aligned _ atomic l false miss _ (lane_cell_read before called aligned _ false)))
    · exact Option.some.inj ((lane_cell_read after called aligned _ true).symm.trans
        (rv_unwritten_lane_frame i called aligned _ atomic l true miss _ (lane_cell_read before called aligned _ true)))

theorem rv_cell_writes_fields {writes : List (Cell × BitVec 32)} {before after : RV.State}
    (execution : RVCellWrites writes before after) :
    after.pc = before.pc ∧ after.rom = before.rom ∧ after.input = before.input := by
  induction execution with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons past write ih =>
    unfold Cell.applyRV at write
    split at write
    · cases Option.some.inj write
      exact ih
    · obtain ⟨pc, input⟩ := writeRV_pc write
      exact ⟨pc.trans ih.1, (writeRV_rom write).trans ih.2.1, input.trans ih.2.2⟩

theorem delegation_effect (kind : Kind) (x10 x11 x12 : RV.Word) (mem : RV.Word → BitVec 8) :
    RV.Delegation.effect kind.delegation x10 x11 x12 mem = keccakF1600 kind.mode x10 x11 mem := by
  cases kind <;> rfl

/-- One split call: the spec's Keccak-f1600 delegation of its worker from the pre-state (at any PC) is its
    post-state. -/
theorem split_call_link {S T : RV.State} (i : Fin 361) (execution : RVExecutesAt i S T) (x : RV.Word) :
    ∃ U, RV.calls [(kindAt i.val).delegation] (S.setPC x) = some U ∧ RV.Same U (T.setPC (x + 4)) := by
  have whole := execution
  obtain ⟨pointer, input, arguments, pointerRead, _, atomic⟩ := execution
  obtain ⟨control, other, controlRead, otherRead, controlWord, aligned⟩ := arguments
  have same := Option.some.inj (otherRead.symm.trans pointerRead)
  subst same
  subst controlWord
  have x10 : S.getReg 10 = BitVec.ofNat 32 (controlAt i.val) := Option.some.inj controlRead
  have x11 : S.getReg 11 = other := Option.some.inj otherRead
  have lanesStep := rv_lanes_step whole pointerRead
  have fits : other.toNat + 4 * (2 * 31) ≤ 2 ^ 32 := by have := other.isLt; omega
  have valid := schedule_spec_valid i
  have controlBound := Split.SetupProofs.controlAt_lt i.isLt
  have controlSpec := control_at_spec i
  have mode : (kindAt i.val).mode < 7 := by cases kindAt i.val <;> decide
  let L := RV.readLanes S.mem other 31
  let L' := f1600Step (kindAt i.val).mode ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩ (i.val / 15) L
  let next := f1600Next (kindAt i.val).mode (i.val % 5) (i.val / 15)
  have effect : RV.Delegation.effect (kindAt i.val).delegation ((S.setPC x).getReg 10) ((S.setPC x).getReg 11)
      ((S.setPC x).getReg 12) (S.setPC x).mem =
      some { writes := RV.writesAt other (RV.laneWords L'), reg := 10, val := RV.Delegation.control next.1 next.2.1 next.2.2 } := by
    rw [delegation_effect]
    change keccakF1600 (kindAt i.val).mode (S.getReg 10) (S.getReg 11) S.mem = _
    rw [x10, x11, controlSpec]
    exact RV.keccakCall_ctl _ f1600Step f1600Next (kindAt i.val).mode (i.val % 5) (i.val / 15)
      next.1 next.2.1 next.2.2 (by omega) (Nat.mod_lt _ (by decide)) (by omega) ⟨rfl, valid⟩ rfl other
      ⟨aligned, by simp only [RV.RAM_END]; omega⟩ S.mem
  have alignedWrites : ∀ aw ∈ RV.writesAt other (RV.laneWords L'), aw.1.toNat % 4 = 0 := by
    intro aw member
    exact (RV.writesAt_in other _ (by omega) (by simp only [RV.RAM_END]; omega) aw member).1
  have nextValue : RV.Delegation.control next.1 next.2.1 next.2.2 = BitVec.ofNat 32 (bump (controlAt i.val)) := by
    simp only [RV.Delegation.control, next, bump_spec i]
  have writesAligned := writes_aligned i other aligned (result i input)
  have untouchedRegister (r : BitVec 5) (r10 : r ≠ 10) (r11 : r ≠ 11) :
      ∀ entry ∈ writes i other (result i input), Cell.register r ≠ entry.1 := by
    intro entry member equal
    rcases List.mem_append.mp member with register | memory
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
      rcases register with rfl | rfl
      · exact r10 (Cell.register.inj equal)
      · exact r11 (Cell.register.inj equal)
    · obtain ⟨lane, _, included⟩ := List.mem_flatMap.mp memory
      split_ifs at included
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at included
        rcases included with rfl | rfl <;> cases equal
      · cases included
  have fields : T.pc = S.pc ∧ T.rom = S.rom ∧ T.input = S.input := by
    obtain ⟨_, _, cellWrites⟩ := atomic
    exact rv_cell_writes_fields cellWrites
  obtain ⟨U, call, landing⟩ := call_same (S := S.setPC x) (T := T) effect alignedWrites fields.2.1 fields.2.2
    (by
      intro r
      by_cases r10 : r = 10
      · subst r10
        simp only [true_and, show (10 : BitVec 5) ≠ 0 by decide, ne_eq, not_false_eq_true, ite_true]
        have written := rv_atomic_writes_reads atomic writesAligned (writes_distinct i other aligned _)
          (cell := .register 10) (value := BitVec.ofNat 32 (bump (controlAt i.val))) (by simp [writes]) (by decide)
        rw [readRV_register] at written
        exact (Option.some.inj written).trans nextValue.symm
      · simp only [r10, false_and, ite_false]
        by_cases r11 : r = 11
        · subst r11
          have kept := (rv_executes_pointer whole pointerRead).2
          rw [readRV_register] at kept
          exact (Option.some.inj kept).trans x11.symm
        · have frame := rv_atomic_writes_frame atomic writesAligned (cell := .register r) trivial
            (untouchedRegister r r10 r11) (readRV_register r S)
          rw [readRV_register] at frame
          exact Option.some.inj frame)
    (by
      intro a alignedA
      rw [storeAll_setPC]
      change RV.read T.mem a 4 = RV.read (S.storeAll (RV.writesAt other (RV.laneWords L'))).mem a 4
      by_cases inside : ∃ j : Fin 62, a = other + BitVec.ofNat 32 (4 * j.val)
      · obtain ⟨j, rfl⟩ := inside
        have spec := read_writesAt_at S [] [] other (RV.laneWords L') fits (by simp) j
        simp only [List.nil_append, List.append_nil] at spec
        rw [spec]
        have l2 : j.val / 2 < 31 := by omega
        have value : L'[j.val / 2].toNat =
            (RV.read T.mem (other + BitVec.ofNat 32 (8 * (j.val / 2))) 4).toNat +
              2 ^ 32 * (RV.read T.mem (other + BitVec.ofNat 32 (8 * (j.val / 2)) + 4) 4).toNat := by
          have step := f1600_step_nat i L ⟨j.val / 2, l2⟩
          have lanes := congrFun lanesStep ⟨j.val / 2, l2⟩
          have combined := step.trans lanes.symm
          rw [rvLanes, Keccak.Proofs.read_lane_toNat] at combined
          exact combined
        obtain ⟨lowHalf, highHalf⟩ := Keccak.Proofs.lane_halves L'[j.val / 2]
          (RV.read T.mem (other + BitVec.ofNat 32 (8 * (j.val / 2))) 4)
          (RV.read T.mem (other + BitVec.ofNat 32 (8 * (j.val / 2)) + 4) 4) value
        have entry : (RV.laneWords L')[j] = L'[j.val / 2].extractLsb' (32 * (j.val % 2)) 32 := by
          simp only [RV.laneWords, Fin.getElem_fin, Vector.getElem_ofFn]
        rw [entry]
        rcases Nat.mod_two_eq_zero_or_one j.val with even | odd
        · rw [even, Nat.mul_zero, lowHalf, show 4 * j.val = 8 * (j.val / 2) by omega]
        · rw [odd, Nat.mul_one, highHalf, show 4 * j.val = 8 * (j.val / 2) + 4 by omega, BitVec.ofNat_add,
            ← BitVec.add_assoc]
          rfl
      · have outside : ∀ j : Fin 62, a ≠ other + BitVec.ofNat 32 (4 * j.val) :=
          fun j same => inside ⟨j, same⟩
        have untouched : ∀ entry ∈ writes i other (result i input), Cell.ram a ≠ entry.1 := by
          intro entry member equal
          rcases List.mem_append.mp member with register | memory
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
            rcases register with rfl | rfl <;> cases equal
          · obtain ⟨lane, _, included⟩ := List.mem_flatMap.mp memory
            split_ifs at included with small
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at included
              have slotBound := ((slots i)[lane]'small).isLt
              rcases included with rfl | rfl
              · apply outside ⟨2 * ((slots i)[lane]'small).val, by omega⟩
                simp only [laneCell, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at equal
                rw [Cell.ram.inj equal]
                congr 2
                dsimp only
                omega
              · apply outside ⟨2 * ((slots i)[lane]'small).val + 1, by omega⟩
                simp only [laneCell, ↓reduceIte] at equal
                rw [Cell.ram.inj equal]
                congr 2
                dsimp only
                omega
            · cases included
        have readable := readable_of_aligned (address := a) alignedA
        have frame := rv_atomic_writes_frame atomic writesAligned (cell := .ram a) alignedA untouched
          (readRV_ram S readable)
        rw [readRV_ram T readable] at frame
        rw [Option.some.inj frame, RV.read_storeAll_other S _ a (by have := a.isLt; omega)
          (writesAt_disjoint other a _ (by omega) fits alignedA outside)])
  exact ⟨U, call, landing⟩

end Airbender.Keccak.Split.Call.Proofs
