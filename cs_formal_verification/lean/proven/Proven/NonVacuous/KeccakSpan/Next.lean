module
public import Proven.NonVacuous.KeccakSpan.Steps
public import Proven.Keccak.Schedule

@[expose] public section

/-! Call `k` of the span as a step of the sequential run: its ports access fourteen distinct cells, its memory
    steps are the run's edges, each port writes a canonical word at its cell at the write clock (x10 the next
    scheduled control word, x11 the pointer), and the invariant holds before call `k + 1`. -/

namespace Airbender.NonVacuous.KeccakSpan
open Arithmetic Trace

local notation "P" => babyBearModulus

variable {mem : Memory} {k : Nat}

theorem ramCell_inj {a b : Nat} (ha : a < 62) (hb : b < 62) (same : ramCell a = ramCell b) : a = b := by
  simp only [ramCell, Cell.ram.injEq] at same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, stateBase, Word.value, limbBase] at values
  omega

/-- The fourteen ports of a call of the span access different cells. -/
theorem ports_nodup (small : k < 649) : ((List.range 14).map (portCell k)).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb same
  simp only [List.mem_range] at ha hb
  have distinct := lanes_nodup small
  have lane (i : Nat) (hi : i < 12) : portCell k (i + 2) =
      ramCell (2 * (lanes k)[i / 2 % 6]'(Nat.mod_lt _ (by decide)) + i % 2) := by
    rw [Nat.add_comm i 2]
    exact portCell_lane k i
  rcases Nat.lt_or_ge a 2 with sa | sa <;> rcases Nat.lt_or_ge b 2 with sb | sb
  · interval_cases a <;> interval_cases b <;> first | rfl | (simp only [portCell] at same; cases same)
  · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
    rw [lane j (by omega)] at same
    interval_cases a <;> (simp only [portCell, ramCell] at same; cases same)
  · obtain ⟨i, rfl⟩ : ∃ i, a = i + 2 := ⟨a - 2, by omega⟩
    rw [lane i (by omega)] at same
    interval_cases b <;> (simp only [portCell, ramCell] at same; cases same)
  · obtain ⟨i, rfl⟩ : ∃ i, a = i + 2 := ⟨a - 2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
    rw [lane i (by omega), lane j (by omega)] at same
    have offsets := ramCell_inj (lane_offset k i) (lane_offset k j) same
    have index : (lanes k)[i / 2 % 6]'(Nat.mod_lt _ (by decide)) = (lanes k)[j / 2 % 6]'(Nat.mod_lt _ (by decide)) := by
      omega
    have position := (List.Nodup.getElem_inj_iff distinct (i := i / 2 % 6) (j := j / 2 % 6)
      (hi := by simp only [Vector.length_toList]; exact Nat.mod_lt _ (by decide))
      (hj := by simp only [Vector.length_toList]; exact Nat.mod_lt _ (by decide))).mp
      (by simpa only [Vector.getElem_toList] using index)
    omega

theorem keys (mem : Memory) (k t : Nat) : (mem.steps k t).map Prod.fst = (List.range 14).map (portCell k) :=
  List.map_fst_zip (by simp [Delegation.Row.ports, Memory.row]; rfl)

/-- The call's memory steps are the run's edges from the memory before it. -/
theorem edges (inv : Inv mem k) (small : k < 649) :
    (mem.row k (1 + 4 * k)).memorySteps = runEdges mem (mem.steps k (1 + 4 * k)) := by
  rw [runEdges_of_nodup mem (by rw [keys]; exact ports_nodup small)]
  apply List.ext_getElem
  · simp [Delegation.Row.memorySteps, Memory.steps, Delegation.Row.ports, Memory.row]
    rfl
  · intro n first second
    have size : Keccak.importedConstraintsMemoryPorts.size = 14 := rfl
    have bound : n < 14 := by
      simpa [Delegation.Row.memorySteps, Delegation.Row.ports, Memory.row, size] using first
    simp only [Delegation.Row.memorySteps, Memory.steps, List.getElem_map, List.getElem_zip, List.getElem_range,
      Array.getElem_toList]
    exact Prod.ext (read inv n bound) rfl

namespace RowInput
variable {x : RowInput}

/-- A valid row writes 16-bit limbs. -/
theorem written_lt (valid : x.Valid) {lane j : Nat} (hl : lane < 6) (hj : j < 4) : x.written lane j < 65536 := by
  rcases RowInput.modes x with hm | hm | hm | hm | hm | hm | hm <;>
  simp only [RowInput.written, hm, ↓reduceIte, Nat.reduceEqDiff, or_self, or_true, true_or] <;>
  split_ifs <;>
  first
    | exact (op0_valid valid).out_lt hj
    | exact (op1_valid valid).out_lt hj
    | exact (op2_valid valid).out_lt hj
    | exact (op3_valid valid).out_lt hj
    | exact (op4_valid valid).out_lt hj
    | exact valid.read _ hl j hj
    | exact valid.read 0 (by decide) j hj

end RowInput

private theorem absurd_one {α : Prop} (h : (0 : Nat) = 1) : α := absurd h (by decide)
private theorem absurd_zero {α : Prop} (h : (1 : Nat) = 0) : α := absurd h (by decide)

theorem next_lt (s : Keccak.ControlState) : s.nextPacked < 65536 := by
  have := s.round.isLt
  simp only [Keccak.ControlState.nextPacked]
  split_ifs <;> omega

/-- Each port's write: at its cell, at the write clock `t + 2`, a canonical word; x10 gets the next control word
    and x11 keeps the pointer. -/
theorem write (inv : Inv mem k) (small : k < 649) (n : Nat) (h : n < 14) :
    ((mem.row k (1 + 4 * k)).writeToken
      (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h))).address =
        (portCell k n).addressCode ∧
      ((mem.row k (1 + 4 * k)).writeToken (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h))).time =
        (((1 + 4 * k : Nat) : ZMod P) + ((2 : Nat) : ZMod P), ((0 : Nat) : ZMod P)) ∧
      ((mem.row k (1 + 4 * k)).writeToken
        (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h))).word.Bounded ∧
      (n = 0 → ((mem.row k (1 + 4 * k)).writeToken
        (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h))).word =
          ⟨(control k).nextPacked, 0⟩) ∧
      (n = 1 → ((mem.row k (1 + 4 * k)).writeToken
        (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h))).word = stateBase) := by
  have valid := valid inv small
  have address := congrArg MemoryToken.address (read inv n h)
  rw [inv.address _ (portCell_mem k n)] at address
  refine ⟨address, ?_, ?_⟩
  · match n, h with
    | 0, _ => rw [port_zero]; rfl
    | 1, _ => rw [port_one]; rfl
    | i + 2, h =>
      have lane := port_lane ⟨i, by omega⟩
      simp only [Nat.add_comm 2 i] at lane
      rw [lane]
      rfl
  match n, h with
  | 0, _ =>
    have word := token_word (by decide)
      (tok := (mem.row k (1 + 4 * k)).writeToken (Keccak.importedConstraintsMemoryPorts[0]'(by decide)))
      (a := (control k).nextPacked) (b := 0) (by rw [port_zero]; rfl) (next_lt (control k)) (by decide)
    refine ⟨(by rw [word]; exact ⟨next_lt (control k), show 0 < 65536 by decide⟩), fun _ => word,
      fun absurd => absurd_one absurd⟩
  | 1, _ =>
    have word := token_word (by decide)
      (tok := (mem.row k (1 + 4 * k)).writeToken (Keccak.importedConstraintsMemoryPorts[1]'(by decide)))
      (by rw [port_one]; rfl) valid.pointer.1 valid.pointer.2.1
    refine ⟨(by rw [word]; exact ⟨valid.pointer.1, valid.pointer.2.1⟩), fun absurd => absurd_zero absurd,
      fun _ => word.trans inv.pointer⟩
  | i + 2, h =>
    have hi : i < 12 := by omega
    have lane := port_lane ⟨i, hi⟩
    simp only [Nat.add_comm 2 i] at lane
    have low := RowInput.written_lt valid (lane := i / 2) (j := 2 * (i % 2)) (by omega) (by omega)
    have high := RowInput.written_lt valid (lane := i / 2) (j := 2 * (i % 2) + 1) (by omega) (by omega)
    have word := token_word (by decide)
      (tok := (mem.row k (1 + 4 * k)).writeToken (Keccak.importedConstraintsMemoryPorts[i + 2]'(by
        change _ < 14; omega)))
      (by
        rw [lane]
        show Nat.pair ((mem.input k (1 + 4 * k)).assignment (17 + 4 * i)).val
          ((mem.input k (1 + 4 * k)).assignment (18 + 4 * i)).val = _
        rw [RowInput.assignment_written_low _ hi, RowInput.assignment_written_high _ hi]) low high
    refine ⟨(by rw [word]; exact ⟨low, high⟩), fun absurd => by omega, fun absurd => by omega⟩

/-- The invariant holds after call `k`, before call `k + 1`. -/
theorem next (inv : Inv mem k) (small : k < 649) :
    Inv (runFinal mem (mem.steps k (1 + 4 * k))) (k + 1) := by
  have nodup : ((mem.steps k (1 + 4 * k)).map Prod.fst).Nodup := by rw [keys]; exact ports_nodup small
  have length : ((List.range 14).map (portCell k)).length = 14 := by simp
  have written (n : Nat) (h : n < 14) : runFinal mem (mem.steps k (1 + 4 * k)) (portCell k n) =
      (mem.row k (1 + 4 * k)).writeToken (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h)) := by
    refine runFinal_of_mem mem nodup (List.mem_iff_getElem.mpr ⟨n, ?_, ?_⟩)
    · simp only [Memory.steps, List.length_zip, List.length_map, List.length_range, Array.length_toList]
      exact Nat.lt_min.mpr ⟨h, h⟩
    · simp only [Memory.steps, List.getElem_zip, List.getElem_map, List.getElem_range, Array.getElem_toList]
      rfl
  have untouched (c : Cell) (absent : c ∉ (List.range 14).map (portCell k)) :
      runFinal mem (mem.steps k (1 + 4 * k)) c = mem c :=
    runFinal_of_not_mem mem (by rw [keys]; exact absent)
  have split (c : Cell) : (∃ n, ∃ h : n < 14, c = portCell k n) ∨ c ∉ (List.range 14).map (portCell k) := by
    by_cases present : c ∈ (List.range 14).map (portCell k)
    · obtain ⟨n, member, same⟩ := List.mem_map.mp present
      exact Or.inl ⟨n, List.mem_range.mp member, same.symm⟩
    · exact Or.inr present
  have clock : ((1 + 4 * k : Nat) : ZMod P) + ((2 : Nat) : ZMod P) = ((1 + 4 * k + 2 : Nat) : ZMod P) := by
    push_cast
    ring
  have clockVal : ((1 + 4 * k + 2 : Nat) : ZMod P).val = 1 + 4 * k + 2 :=
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)
  constructor
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h]
      exact (write inv small n h).1
    · rw [untouched c absent]
      exact inv.address c member
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h, (write inv small n h).2.1, Nat.cast_zero]
    · rw [untouched c absent]
      exact inv.high c member
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h, (write inv small n h).2.1, clock, clockVal]
      omega
    · rw [untouched c absent]
      exact Nat.le_trans (inv.time c member) (by omega)
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h]
      exact (write inv small n h).2.2.1
    · rw [untouched c absent]
      exact inv.words c member
  · rw [show Cell.register 11 = portCell k 1 from rfl, written 1 (by decide)]
    exact (write inv small 1 (by decide)).2.2.2.2 rfl
  · rw [show Cell.register 10 = portCell k 0 from rfl, written 0 (by decide)]
    rw [(write inv small 0 (by decide)).2.2.2.1 rfl, control_eq (by omega : k < 650),
      control_eq (by omega : k + 1 < 650)]
    have step := Keccak.Proofs.schedule_next ⟨k, small⟩
    simp only at step
    rw [step]

end Airbender.NonVacuous.KeccakSpan
