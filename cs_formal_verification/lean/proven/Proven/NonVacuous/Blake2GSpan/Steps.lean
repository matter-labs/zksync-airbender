module
public import Proven.NonVacuous.Blake2GSpan.Block

@[expose] public section

/-! A G row's memory steps under the span invariant: each port reads its cell's current token (so the row's steps
    are the sequential run's edges), and the memory after the row satisfies the invariant at the next invocation
    clock (`t + 4`). -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic Trace

local notation "P" => babyBearModulus

/-- An indirect port at `base + 4 * offset` addresses that RAM cell. -/
theorem indirect_code {w : Nat → ZMod P} {port : Verification.IndirectPort} {base : Word} {offset : Nat}
    (bounded : base.Bounded) (room : base.lo + 4 * offset < 65536)
    (shape : MemoryAddress.code (.indirect port) w = Nat.pair 1 (Nat.pair
      ((base.lo : ZMod P) + ((4 : Nat) : ZMod P) * (offset : ZMod P) + ((0 : Nat) : ZMod P)).val
      ((base.hi : ZMod P)).val)) :
    MemoryAddress.code (.indirect port) w = (ramCell base offset).addressCode := by
  have hi := bounded.2
  simp only [limbBase] at hi
  have sum : (base.lo : ZMod P) + ((4 : Nat) : ZMod P) * (offset : ZMod P) + ((0 : Nat) : ZMod P) =
      ((base.lo + 4 * offset : Nat) : ZMod P) := by
    push_cast
    ring
  rw [shape, ramCell_code bounded room, sum, ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega),
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)]

variable {mem : Memory} {t : Nat}

/-- Each port reads its cell's current token. -/
theorem read (inv : Inv mem t) (n : Nat) (h : n < 9) :
    readToken (mem.input t).assignment (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h)) =
      mem (mem.ports[n]'h) := by
  obtain ⟨-, -, -, o1, o2, o3, o4, o5, o6⟩ := controls_facts mem
  have cell (j : Fin 9) := ports_mem inv j
  have x10 : (mem (.register 10)).word.Bounded := inv.words _ (cell 0)
  have x11 : (mem (.register 11)).word.Bounded := inv.words _ (cell 5)
  have state : (mem (.register 10)).word.lo = 0 := by rw [inv.state]; rfl
  have message : (mem (.register 11)).word.lo = 64 := by rw [inv.message]; rfl
  interval_cases n
  · exact read_eq (by decide) (tok := mem (mem.ports[0]'h)) rfl rfl
      ((rfl : _ = mem.ports[(0 : Fin 9)].addressCode).trans (inv.address _ (cell 0)).symm) rfl rfl rfl rfl rfl
      (inv.high _ (cell 0)) (inv.words _ (cell 0))
  · exact read_eq (by decide) (tok := mem (mem.ports[1]'h)) rfl rfl
      (by
        refine Eq.trans ?_ (inv.address _ (cell 1)).symm
        exact indirect_code (offset := mem.controls[1]) x10 (by omega) rfl) rfl rfl rfl rfl rfl
      (inv.high _ (cell 1)) (inv.words _ (cell 1))
  · exact read_eq (by decide) (tok := mem (mem.ports[2]'h)) rfl rfl
      (by
        refine Eq.trans ?_ (inv.address _ (cell 2)).symm
        exact indirect_code (offset := mem.controls[2]) x10 (by omega) rfl) rfl rfl rfl rfl rfl
      (inv.high _ (cell 2)) (inv.words _ (cell 2))
  · exact read_eq (by decide) (tok := mem (mem.ports[3]'h)) rfl rfl
      (by
        refine Eq.trans ?_ (inv.address _ (cell 3)).symm
        exact indirect_code (offset := mem.controls[3]) x10 (by omega) rfl) rfl rfl rfl rfl rfl
      (inv.high _ (cell 3)) (inv.words _ (cell 3))
  · exact read_eq (by decide) (tok := mem (mem.ports[4]'h)) rfl rfl
      (by
        refine Eq.trans ?_ (inv.address _ (cell 4)).symm
        exact indirect_code (offset := mem.controls[4]) x10 (by omega) rfl) rfl rfl rfl rfl rfl
      (inv.high _ (cell 4)) (inv.words _ (cell 4))
  · exact read_eq (by decide) (tok := mem (mem.ports[5]'h)) rfl rfl
      ((rfl : _ = mem.ports[(5 : Fin 9)].addressCode).trans (inv.address _ (cell 5)).symm) rfl rfl rfl rfl rfl
      (inv.high _ (cell 5)) (inv.words _ (cell 5))
  · exact read_eq (by decide) (tok := mem (mem.ports[6]'h)) rfl rfl
      (by
        refine Eq.trans ?_ (inv.address _ (cell 6)).symm
        exact indirect_code (offset := mem.controls[5]) x11 (by omega) rfl) rfl rfl rfl rfl rfl
      (inv.high _ (cell 6)) (inv.words _ (cell 6))
  · exact read_eq (by decide) (tok := mem (mem.ports[7]'h)) rfl rfl
      (by
        refine Eq.trans ?_ (inv.address _ (cell 7)).symm
        exact indirect_code (offset := mem.controls[6]) x11 (by omega) rfl) rfl rfl rfl rfl rfl
      (inv.high _ (cell 7)) (inv.words _ (cell 7))
  · exact read_eq (by decide) (tok := mem (mem.ports[8]'h)) rfl rfl
      ((rfl : _ = mem.ports[(8 : Fin 9)].addressCode).trans (inv.address _ (cell 8)).symm) rfl rfl rfl rfl
      inv.control.1.symm (inv.high _ (cell 8)) (inv.words _ (cell 8))

theorem keys (mem : Memory) (t : Nat) : (mem.steps t).map Prod.fst = mem.ports.toList :=
  List.map_fst_zip (by simp [Delegation.Row.ports, Memory.row]; rfl)

/-- The row's memory steps are the run's edges from the memory before it. -/
theorem edges (inv : Inv mem t) : (mem.row t).memorySteps = runEdges mem (mem.steps t) := by
  rw [runEdges_of_nodup mem (by rw [keys]; exact ports_nodup inv)]
  apply List.ext_getElem
  · simp [Delegation.Row.memorySteps, Memory.steps, Delegation.Row.ports, Memory.row]
    rfl
  · intro n first second
    have size : Blake2G.importedConstraintsMemoryPorts.size = 9 := rfl
    have bound : n < 9 := by
      simpa [Delegation.Row.memorySteps, Delegation.Row.ports, Memory.row, size] using first
    simp only [Delegation.Row.memorySteps, Memory.steps, List.getElem_map, List.getElem_zip, Vector.getElem_toList,
      Array.getElem_toList]
    exact Prod.ext (read inv n bound) rfl

/-- Each port's write: at its cell, at the write clock `t + 2`, a canonical word; x10 and x11 keep the pointers
    and x12 gets the controller's next eight-bit control word. -/
theorem write (inv : Inv mem t) (step : t % 4 = 1) (room : t + 2 < timestampBase) (n : Nat) (h : n < 9) :
    ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).address =
        (mem.ports[n]'h).addressCode ∧
      ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).time =
        ((t : ZMod P) + ((2 : Nat) : ZMod P), ((0 : Nat) : ZMod P)) ∧
      ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).word.Bounded ∧
      (n = 0 → ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).word =
        stateBase) ∧
      (n = 5 → ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).word =
        messageBase) ∧
      (n = 8 →
        ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).word.hi = 0 ∧
        ((mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h))).word.lo <
          256) := by
  have valid := valid inv step room
  have address := congrArg MemoryToken.address (read inv n h)
  have cell : mem.ports[n]'h ∈ cells := ports_mem inv ⟨n, h⟩
  rw [inv.address _ cell] at address
  refine ⟨address, ?_, ?_⟩
  · interval_cases n <;> rfl
  have a := valid.a
  have b := valid.b
  have c := valid.c
  have d := valid.d
  have mx := valid.mx
  have my := valid.my
  have sp := valid.statePointer
  have mp := valid.messagePointer
  simp only [Word.Bounded, limbBase] at a b c d mx my sp mp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, xe0, xe1, xe2, xe3, xf0, xf1, xf2, xf3⟩ := valid.xors
  obtain ⟨next, -⟩ := controls_facts mem
  have state : (mem (.register 10)).word = stateBase := inv.state
  have message : (mem (.register 11)).word = messageBase := inv.message
  interval_cases n
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[0]'(by decide)))
      rfl sp.1.1 sp.1.2
    refine ⟨⟨by rw [word]; exact sp.1.1, by rw [word]; exact sp.1.2⟩, fun _ => word.trans state, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[1]'(by decide)))
      rfl (a := (mem.input t).a2lo) (b := (mem.input t).a2hi) (by simp only [RowInput.a2lo]; omega)
      (by simp only [RowInput.a2hi]; omega)
    refine ⟨by rw [word]; simp only [Word.Bounded, limbBase, RowInput.a2lo, RowInput.a2hi]; omega,
      by omega, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[2]'(by decide)))
      rfl (a := (mem.input t).b2lo) (b := (mem.input t).b2hi) (by simp only [RowInput.b2lo]; omega)
      (by simp only [RowInput.b2hi]; omega)
    refine ⟨by rw [word]; simp only [Word.Bounded, limbBase, RowInput.b2lo, RowInput.b2hi]; omega,
      by omega, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[3]'(by decide)))
      rfl (a := (mem.input t).c2lo) (b := (mem.input t).c2hi) (by simp only [RowInput.c2lo]; omega)
      (by simp only [RowInput.c2hi]; omega)
    refine ⟨by rw [word]; simp only [Word.Bounded, limbBase, RowInput.c2lo, RowInput.c2hi]; omega,
      by omega, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[4]'(by decide)))
      rfl (a := (mem.input t).d2lo) (b := (mem.input t).d2hi) (by simp only [RowInput.d2lo]; omega)
      (by simp only [RowInput.d2hi]; omega)
    refine ⟨by rw [word]; simp only [Word.Bounded, limbBase, RowInput.d2lo, RowInput.d2hi]; omega,
      by omega, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[5]'(by decide)))
      rfl mp.1.1 mp.1.2
    refine ⟨⟨by rw [word]; exact mp.1.1, by rw [word]; exact mp.1.2⟩, by omega, fun _ => word.trans message,
      by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[6]'(by decide)))
      rfl mx.1 mx.2
    refine ⟨⟨by rw [word]; exact mx.1, by rw [word]; exact mx.2⟩, by omega, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[7]'(by decide)))
      rfl my.1 my.2
    refine ⟨⟨by rw [word]; exact my.1, by rw [word]; exact my.2⟩, by omega, by omega, by omega⟩
  · have word := token_word (by decide)
      (tok := (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[8]'(by decide)))
      rfl (a := mem.controls[0]) (b := 0) (by omega) (by omega)
    refine ⟨⟨by rw [word]; show mem.controls[0] < 65536; omega, by rw [word]; show 0 < 65536; omega⟩, by omega,
      by omega,
      fun _ => ⟨by rw [word], by rw [word]; exact next⟩⟩

/-- The invariant holds after the row, at the next invocation clock. -/
theorem next (inv : Inv mem t) (step : t % 4 = 1) (room : t + 2 < timestampBase) :
    Inv (runFinal mem (mem.steps t)) (t + 4) := by
  have nodup : ((mem.steps t).map Prod.fst).Nodup := by rw [keys]; exact ports_nodup inv
  have length : mem.ports.toList.length = 9 := by simp
  have written (n : Nat) (h : n < 9) : runFinal mem (mem.steps t) (mem.ports[n]'h) =
      (mem.row t).writeToken (Blake2G.importedConstraintsMemoryPorts[n]'(by change n < 9; exact h)) := by
    refine runFinal_of_mem mem nodup (List.mem_iff_getElem.mpr ⟨n, ?_, ?_⟩)
    · simp only [Memory.steps, List.length_zip, List.length_map, Array.length_toList, length]
      exact Nat.lt_min.mpr ⟨h, h⟩
    · simp only [Memory.steps, List.getElem_zip, List.getElem_map, Vector.getElem_toList, Array.getElem_toList]
      rfl
  have untouched (c : Cell) (absent : c ∉ mem.ports.toList) : runFinal mem (mem.steps t) c = mem c :=
    runFinal_of_not_mem mem (by rw [keys]; exact absent)
  have split (c : Cell) : (∃ n, ∃ h : n < 9, c = mem.ports[n]'h) ∨ c ∉ mem.ports.toList := by
    by_cases present : c ∈ mem.ports.toList
    · obtain ⟨n, h, same⟩ := List.mem_iff_getElem.mp present
      exact Or.inl ⟨n, length ▸ h, by rw [← same, Vector.getElem_toList]⟩
    · exact Or.inr present
  have clock : ((t : ZMod P) + ((2 : Nat) : ZMod P)).val = t + 2 := by
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by simp only [timestampBase] at room; unfold babyBearModulus; omega)]
  constructor
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h]
      exact (write inv step room n h).1
    · rw [untouched c absent]
      exact inv.address c member
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h, (write inv step room n h).2.1, Nat.cast_zero]
    · rw [untouched c absent]
      exact inv.high c member
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h, (write inv step room n h).2.1, clock]
      omega
    · rw [untouched c absent]
      exact Nat.le_trans (inv.time c member) (by omega)
  · intro c member
    rcases split c with ⟨n, h, rfl⟩ | absent
    · rw [written n h]
      exact (write inv step room n h).2.2.1
    · rw [untouched c absent]
      exact inv.words c member
  · rw [show Cell.register 10 = mem.ports[0]'(by decide) from rfl, written 0 (by decide)]
    exact (write inv step room 0 (by decide)).2.2.2.1 rfl
  · rw [show Cell.register 11 = mem.ports[5]'(by decide) from rfl, written 5 (by decide)]
    exact (write inv step room 5 (by decide)).2.2.2.2.1 rfl
  · rw [show Cell.register 12 = mem.ports[8]'(by decide) from rfl, written 8 (by decide)]
    exact (write inv step room 8 (by decide)).2.2.2.2.2 rfl

end Airbender.NonVacuous.Blake2GSpan
