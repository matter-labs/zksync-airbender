module
public import Proven.NonVacuous.Blake2RoundSpan.Ports
public import Proven.NonVacuous.Blake2RoundSpan.FinalEval

@[expose] public section

/-! A round row's memory steps under the span invariant: its steps are the sequential run's edges (each port reads
    its cell's current token), and the memory after the row satisfies the invariant at the next invocation clock
    (`t + 4`) and the next round (the control word's round bit shifted). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Trace Blake2GSpan

local notation "P" => babyBearModulus
local notation "ports" => Blake2Round.importedConstraintsMemoryPorts

variable {mem : Memory} {t k : Nat}

theorem keys (mem : Memory) (t : Nat) (k : Fin 10) : (stepsAt mem t k).map Prod.fst = cells :=
  List.map_fst_zip (by simp [Delegation.Row.ports, rowAt', cells]; rfl)

/-- The row's memory steps are the run's edges from the memory before it. -/
theorem edges (inv : Inv mem t k) (hk : k < 10) :
    (rowAt' mem t ⟨k, hk⟩).memorySteps = runEdges mem (stepsAt mem t ⟨k, hk⟩) := by
  rw [runEdges_of_nodup mem (by rw [keys]; exact cells_nodup)]
  apply List.ext_getElem
  · simp [Delegation.Row.memorySteps, stepsAt, Delegation.Row.ports, rowAt', cells]
    rfl
  · intro n first second
    have size : Blake2Round.importedConstraintsMemoryPorts.size = 43 := rfl
    have bound : n < 43 := by
      have := first
      simp only [Delegation.Row.memorySteps, Delegation.Row.ports, rowAt', List.length_map,
        Array.length_toList] at this
      omega
    simp only [Delegation.Row.memorySteps, stepsAt, List.getElem_map, List.getElem_zip, Array.getElem_toList]
    refine Prod.ext ?_ rfl
    simp only [cells, List.getElem_map, List.getElem_range]
    exact read inv hk n bound

/-- The written value of a port: its write columns, or its read columns for a read-only port. -/
theorem write_value (hk : k < 10) (j : Nat) (hj : j < 43) :
    ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).value =
      (ports[j]'(by change j < 43; exact hj)).writeCode (inputAt mem t ⟨k, hk⟩).assignment (p := P) := rfl

/-- Each port's write: at its cell, at the write clock `t + 2`, a canonical word; x10 and x11 keep the pointers and
    x12 gets the next round's control word. -/
theorem write (inv : Inv mem t k) (hk : k < 10) (step : t % 4 = 1) (room : t + 2 < timestampBase) (j : Nat)
    (hj : j < 43) :
    ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).address = (cellAt j).addressCode ∧
      ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).time =
        ((t : ZMod P) + ((2 : Nat) : ZMod P), ((0 : Nat) : ZMod P)) ∧
      ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).word.Bounded ∧
      (j = 0 → ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).word = stateBase) ∧
      (j = 25 → ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).word = messageBase) ∧
      (j = 42 →
        ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).word = controlWord (k + 1)) := by
  have valid := valid inv hk step room
  have readToken := read inv hk j hj
  have cell := cellAt_mem (j := j) hj
  have clock := port_clock ⟨j, hj⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← inv.address _ cell, ← readToken]
    rfl
  · have low := (inputAt mem t ⟨k, hk⟩).assignment_invocation (p := P)
    have high := (inputAt mem t ⟨k, hk⟩).assignment_invocationHigh (p := P)
    simp only [Delegation.Row.writeToken, rowAt', Delegation.Row.columns, Blake2Round.delegation_columns, rawPair,
      clock]
    exact Prod.ext (congrArg (· + ((2 : Nat) : ZMod P)) low) high
  -- a read-only port writes back the word it read
  have readOnly (none : (ports[j]'(by change j < 43; exact hj)).writeValue = none) :
      ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).word = (mem (cellAt j)).word := by
    have value : ((rowAt' mem t ⟨k, hk⟩).writeToken (ports[j]'(by change j < 43; exact hj))).value =
        (Trace.readToken (inputAt mem t ⟨k, hk⟩).assignment (p := P) (ports[j]'(by change j < 43; exact hj))).value := by
      rw [write_value hk j hj, MemoryPort.writeCode, none, Option.getD_none]
      rfl
    rw [← readToken]
    simp only [MemoryToken.word, value]
  obtain ⟨r0, w0, a0, r25, w25, a25, r42, w42, a42⟩ := port_registers
  by_cases zero : j = 0
  · subst zero
    rw [readOnly w0]
    exact ⟨inv.words _ cell, fun _ => inv.state, by omega, by omega⟩
  by_cases state : j < 25
  · obtain ⟨i, rfl⟩ : ∃ i, j = 1 + i := ⟨j - 1, by omega⟩
    obtain ⟨-, writeValue, -⟩ := port_state ⟨i, by omega⟩
    have bounds : (inputAt mem t ⟨k, hk⟩).portLimb i 2 < 65536 ∧ (inputAt mem t ⟨k, hk⟩).portLimb i 3 < 65536 := by
      unfold RowInput.portLimb
      simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceSub]
      split_ifs with low
      · have word := valid.state i low
        simp only [Word.Bounded, limbBase] at word
        have slots (h : Nat) : (i < 4 → (inputAt mem t ⟨k, hk⟩).finalSlot i h 4 + 128 *
            (inputAt mem t ⟨k, hk⟩).finalSlot i h 5 < 65536) ∧ (¬ i < 4 → (inputAt mem t ⟨k, hk⟩).finalSlot i h 4 +
            256 * (inputAt mem t ⟨k, hk⟩).finalSlot i h 5 < 65536) := by
          constructor
          · intro four
            obtain ⟨-, -, -, -, s4, s5⟩ := (valid.finalSlot_bounds (i := i) (h := h) (by omega)).1 four
            omega
          · intro four
            obtain ⟨-, -, -, -, s4, s5⟩ := (valid.finalSlot_bounds (i := i) (h := h) (by omega)).2 (by omega)
            omega
        have zero := slots 0
        have one := slots 1
        unfold RowInput.finalLimb RowInput.limb
        simp only [Nat.reduceEqDiff, ↓reduceIte]
        split_ifs <;> omega
      · have word := valid.out (L := i - 8) (by omega)
        simp only [Word.Bounded, limbBase] at word
        unfold RowInput.limb
        split_ifs <;> omega
    have word := token_word (by decide)
      (tok := (rowAt' mem t ⟨k, hk⟩).writeToken (ports[1 + i]'(by change 1 + i < 43; omega)))
      (a := (inputAt mem t ⟨k, hk⟩).portLimb i 2) (b := (inputAt mem t ⟨k, hk⟩).portLimb i 3) (by
        rw [write_value hk (1 + i) (by omega), MemoryPort.writeCode, writeValue, Option.getD_some]
        simp only [WordColumns.code, WordColumns.evaluate, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        rw [show (inputAt mem t ⟨k, hk⟩).assignment (p := P) (7 + 4 * i) = _ from
          (inputAt mem t ⟨k, hk⟩).assignment_portWrite (h := 0) (by omega) (by omega),
          (inputAt mem t ⟨k, hk⟩).assignment_portWrite (h := 1) (by omega) (by omega)]) bounds.1 bounds.2
    rw [word]
    exact ⟨⟨bounds.1, bounds.2⟩, by omega, by omega, by omega⟩
  by_cases eleven : j = 25
  · subst eleven
    rw [readOnly w25]
    exact ⟨inv.words _ cell, by omega, fun _ => inv.message, by omega⟩
  by_cases message : j < 42
  · obtain ⟨i, rfl⟩ : ∃ i, j = 26 + i := ⟨j - 26, by omega⟩
    obtain ⟨-, writeValue, -⟩ := port_message ⟨i, by omega⟩
    rw [readOnly writeValue]
    exact ⟨inv.words _ cell, by omega, by omega, by omega⟩
  obtain rfl : j = 42 := by omega
  have next : 16 * (2 ^ k % 512) = 8 * 2 ^ (k + 1) % 8192 := by interval_cases k <;> rfl
  have word := token_word (by decide)
    (tok := (rowAt' mem t ⟨k, hk⟩).writeToken (ports[42]'(by decide))) (a := 0) (b := 16 * (2 ^ k % 512)) (by
      rw [write_value hk 42 (by decide), MemoryPort.writeCode, w42, Option.getD_some]
      rfl) (by omega) (by
        have : 2 ^ k % 512 < 512 := Nat.mod_lt _ (by decide)
        omega)
  rw [word, next]
  refine ⟨⟨by simp [limbBase], ?_⟩, by omega, by omega, fun _ => rfl⟩
  simp only [limbBase]
  exact lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

/-- The invariant holds after the row, at the next invocation clock and round. -/
theorem next (inv : Inv mem t k) (hk : k < 10) (step : t % 4 = 1) (room : t + 2 < timestampBase) :
    Inv (runFinal mem (stepsAt mem t ⟨k, hk⟩)) (t + 4) (k + 1) := by
  have nodup : ((stepsAt mem t ⟨k, hk⟩).map Prod.fst).Nodup := by rw [keys]; exact cells_nodup
  have written (n : Nat) (h : n < 43) : runFinal mem (stepsAt mem t ⟨k, hk⟩) (cellAt n) =
      (rowAt' mem t ⟨k, hk⟩).writeToken (ports[n]'(by change n < 43; exact h)) := by
    refine runFinal_of_mem mem nodup (List.mem_iff_getElem.mpr ⟨n, ?_, ?_⟩)
    · simp only [stepsAt, List.length_zip, List.length_map, Array.length_toList, cells, List.length_range]
      exact Nat.lt_min.mpr ⟨h, h⟩
    · simp only [stepsAt, List.getElem_zip, List.getElem_map, Array.getElem_toList, cells, List.getElem_range]
      rfl
  have split (c : Cell) (member : c ∈ cells) : ∃ n, ∃ h : n < 43, c = cellAt n := by
    obtain ⟨n, present, rfl⟩ := List.mem_map.mp member
    exact ⟨n, List.mem_range.mp present, rfl⟩
  have clock : ((t : ZMod P) + ((2 : Nat) : ZMod P)).val = t + 2 := by
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by simp only [timestampBase] at room; unfold babyBearModulus; omega)]
  constructor
  · intro c member
    obtain ⟨n, h, rfl⟩ := split c member
    rw [written n h]
    exact (write inv hk step room n h).1
  · intro c member
    obtain ⟨n, h, rfl⟩ := split c member
    rw [written n h, (write inv hk step room n h).2.1, Nat.cast_zero]
  · intro c member
    obtain ⟨n, h, rfl⟩ := split c member
    rw [written n h, (write inv hk step room n h).2.1, clock]
    omega
  · intro c member
    obtain ⟨n, h, rfl⟩ := split c member
    rw [written n h]
    exact (write inv hk step room n h).2.2.1
  · rw [show Cell.register 10 = cellAt 0 from rfl, written 0 (by decide)]
    exact (write inv hk step room 0 (by decide)).2.2.2.1 rfl
  · rw [show Cell.register 11 = cellAt 25 from rfl, written 25 (by decide)]
    exact (write inv hk step room 25 (by decide)).2.2.2.2.1 rfl
  · rw [show Cell.register 12 = cellAt 42 from rfl, written 42 (by decide)]
    exact (write inv hk step room 42 (by decide)).2.2.2.2.2 rfl

end Airbender.NonVacuous.Blake2RoundSpan
