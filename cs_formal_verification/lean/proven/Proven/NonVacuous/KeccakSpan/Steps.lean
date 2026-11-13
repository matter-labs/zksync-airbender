module
public import Proven.NonVacuous.KeccakSpan.Ports

@[expose] public section

/-! Call `k` of the span under the invariant: its inputs are valid, each port reads its cell's current token (so
    the row's steps are the sequential run's edges), each port writes a canonical word at its cell at the write
    clock (x10 the next scheduled control word, x11 the pointer), and the memory after the call satisfies the
    invariant before call `k + 1`. -/

namespace Airbender.NonVacuous.KeccakSpan
open Arithmetic Trace

local notation "P" => babyBearModulus

variable {mem : Memory} {k : Nat}

theorem portCell_lane (k i : Nat) :
    portCell k (2 + i) = ramCell (2 * (lanes k)[i / 2 % 6]'(Nat.mod_lt _ (by decide)) + i % 2) := by
  simp only [portCell, show ¬2 + i = 0 by omega, show ¬2 + i = 1 by omega, ↓reduceIte, show 2 + i - 2 = i by omega]

theorem lane_offset (k i : Nat) :
    2 * (lanes k)[i / 2 % 6]'(Nat.mod_lt _ (by decide)) + i % 2 < 62 := by
  have := lanes_bound k ⟨i / 2 % 6, Nat.mod_lt _ (by decide)⟩
  simp only [Fin.getElem_fin] at this
  omega

/-- Under the invariant the call's inputs are valid. -/
theorem valid (inv : Inv mem k) (small : k < 649) : (mem.input k (1 + 4 * k)).Valid where
  read lane _ j _ := by
    have bounded := inv.words _ (portCell_mem k (2 + 2 * lane + j / 2))
    simp only [Word.Bounded, limbBase] at bounded
    simp only [Memory.input]
    split_ifs <;> omega
  pointer := by
    show (mem (.register 11)).word.lo < 65536 ∧ (mem (.register 11)).word.hi < 65536 ∧
      (mem (.register 11)).word.lo % 256 = 0
    rw [inv.pointer]
    decide
  previous n _ := Nat.lt_of_le_of_lt (inv.time _ (portCell_mem k n)) (by simp only [Memory.input]; omega)
  invocation := by show (1 + 4 * k) % 4 = 1; omega
  room := by show 1 + 4 * k + 2 < timestampBase; simp only [timestampBase]; omega

/-- Each port reads its cell's current token. -/
theorem read (inv : Inv mem k) (n : Nat) (h : n < 14) :
    readToken (mem.input k (1 + 4 * k)).assignment
        (Keccak.importedConstraintsMemoryPorts[n]'(by change n < 14; exact h)) =
      mem (portCell k n) := by
  have cell := portCell_mem k n
  have x11 : (mem (.register 11)).word = stateBase := inv.pointer
  match n, h with
  | 0, _ =>
    rw [port_zero]
    have word := inv.control
    exact read_eq (by decide) (tok := mem (portCell k 0)) rfl rfl
      ((rfl : _ = (portCell k 0).addressCode).trans (inv.address _ cell).symm)
      (clock_low _ (k := 0) (by decide)) (clock_high _ (k := 0) (by decide))
      (by show (((control k).packed : Nat) : ZMod P) = _; rw [show portCell k 0 = .register 10 from rfl, word])
      rfl (by rw [show portCell k 0 = .register 10 from rfl, word]; rfl) (inv.high _ cell) (inv.words _ cell)
  | 1, _ =>
    rw [port_one]
    exact read_eq (by decide) (tok := mem (portCell k 1)) rfl rfl
      ((rfl : _ = (portCell k 1).addressCode).trans (inv.address _ cell).symm)
      (clock_low _ (k := 1) (by decide)) (clock_high _ (k := 1) (by decide)) rfl rfl rfl
      (inv.high _ cell) (inv.words _ cell)
  | i + 2, h =>
    have hi : i < 12 := by omega
    have layout : Keccak.importedConstraintsMemoryPorts[i + 2]'(by change _ < 14; omega) =
        ⟨⟨2, #v[228 + 3 * i, 229 + 3 * i], 230 + 3 * i⟩,
          .indirect ⟨11, i, #v[13, 14], 8, some (7 + i / 2), 4 * (i % 2), #v[15 + 4 * i, 16 + 4 * i],
            some #v[17 + 4 * i, 18 + 4 * i]⟩,
          .u16 #v[15 + 4 * i, 16 + 4 * i], some (.u16 #v[17 + 4 * i, 18 + 4 * i])⟩ := by
      have lane := port_lane ⟨i, hi⟩
      simp only [Nat.add_comm 2 i] at lane
      exact lane
    rw [layout]
    have lanePort : portCell k (i + 2) = ramCell (2 * (lanes k)[i / 2]'(by omega) + i % 2) := by
      simp only [portCell, show ¬i + 2 = 0 by omega, show ¬i + 2 = 1 by omega, ↓reduceIte,
        show i + 2 - 2 = i by omega, Nat.mod_eq_of_lt (show i / 2 < 6 by omega)]
    have offset : 2 * (lanes k)[i / 2]'(by omega) + i % 2 < 62 := by
      have := lanes_bound k ⟨i / 2, by omega⟩
      simp only [Fin.getElem_fin] at this
      omega
    have word (j : Nat) (hj : j < 2) : (mem.input k (1 + 4 * k)).read (i / 2) (2 * (i % 2) + j) =
        if j = 0 then (mem (portCell k (i + 2))).word.lo else (mem (portCell k (i + 2))).word.hi := by
      simp only [Memory.input, show 2 + 2 * (i / 2) + (2 * (i % 2) + j) / 2 = i + 2 by omega]
      interval_cases j <;> simp
    refine read_eq (by decide) (tok := mem (portCell k (i + 2))) rfl rfl ?_
      (by rw [show 228 + 3 * i = 222 + 3 * (i + 2) by omega]; exact clock_low _ (by omega))
      (by rw [show 229 + 3 * i = 223 + 3 * (i + 2) by omega]; exact clock_high _ (by omega))
      (by rw [RowInput.assignment_read_low _ hi]; have := word 0 (by decide); simp only [add_zero] at this
          rw [this]; rfl)
      (by rw [RowInput.assignment_read_high _ hi, word 1 (by decide)]; rfl) rfl (inv.high _ cell) (inv.words _ cell)
    rw [inv.address _ cell, lanePort, ramCell_code offset]
    have pointer : (mem.input k (1 + 4 * k)).pointer = stateBase := x11
    have sum : (mem.input k (1 + 4 * k)).assignment (p := P) 13 + ((8 : Nat) : ZMod P) *
        (mem.input k (1 + 4 * k)).assignment (7 + i / 2) + ((4 * (i % 2) : Nat) : ZMod P) =
        ((4 * (2 * (lanes k)[i / 2]'(by omega) + i % 2) : Nat) : ZMod P) := by
      rw [RowInput.assignment_index _ (by omega), RowInput.assignment_13, pointer]
      simp only [stateBase, RowInput.indices, Memory.input, lanes]
      push_cast
      ring
    simp only [MemoryAddress.code, Verification.IndirectPort.rawAddress, Option.elim, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, sum, RowInput.assignment_14, pointer]
    rw [ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega),
      ZMod.val_natCast_of_lt (by unfold babyBearModulus; simp only [stateBase]; omega)]
    rfl

end Airbender.NonVacuous.KeccakSpan
