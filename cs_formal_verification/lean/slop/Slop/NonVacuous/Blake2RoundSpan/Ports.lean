module
public import Slop.NonVacuous.Blake2RoundSpan.Block
public import Slop.NonVacuous.SequentialRun

@[expose] public section

/-! The 43 ports of the round row (`Blake2Round.importedConstraintsMemoryPorts`), by family: x10, the 24 state
    words at x10 (read and written), x11, the 16 message words at x11 (read only), x12 (read and written). Under the
    span invariant each port reads its cell's current token. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Trace Blake2GSpan

local notation "P" => babyBearModulus
local notation "ports" => Blake2Round.importedConstraintsMemoryPorts

theorem port_clock (j : Fin 43) : ports[j.val].clock = ⟨2, #v[632 + 3 * j.val, 633 + 3 * j.val], 634 + 3 * j.val⟩ := by
  fin_cases j <;> rfl

theorem port_state (i : Fin 24) :
    (ports[1 + i.val]'(by change 1 + i.val < 43; omega)).readValue = .u16 #v[5 + 4 * i.val, 5 + 4 * i.val + 1] ∧
      (ports[1 + i.val]'(by change 1 + i.val < 43; omega)).writeValue = some (.u16 #v[7 + 4 * i.val, 7 + 4 * i.val + 1]) ∧
      (ports[1 + i.val]'(by change 1 + i.val < 43; omega)).address = .indirect ⟨10, i.val, #v[3, 4], 0, none, 4 * i.val, #v[5 + 4 * i.val, 6 + 4 * i.val],
        some #v[7 + 4 * i.val, 8 + 4 * i.val]⟩ := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem port_message (i : Fin 16) :
    (ports[26 + i.val]'(by change 26 + i.val < 43; omega)).readValue = .u16 #v[103 + 2 * i.val, 103 + 2 * i.val + 1] ∧
      (ports[26 + i.val]'(by change 26 + i.val < 43; omega)).writeValue = none ∧
      (ports[26 + i.val]'(by change 26 + i.val < 43; omega)).address = .indirect ⟨11, i.val, #v[101, 102], 0, none, 4 * i.val,
        #v[103 + 2 * i.val, 104 + 2 * i.val], none⟩ := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem port_registers :
    ports[0].readValue = .u16 #v[3, 4] ∧ ports[0].writeValue = none ∧ ports[0].address = .constantRegister 10 ∧
      ports[25].readValue = .u16 #v[101, 102] ∧ ports[25].writeValue = none ∧
      ports[25].address = .constantRegister 11 ∧
      ports[42].readValue = .u16 #v[135, 136] ∧ ports[42].writeValue = some (.u16 #v[137, 138]) ∧
      ports[42].address = .constantRegister 12 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {mem : Memory} {t k : Nat}

/-- The state word limbs the row reads are the tokens at the state cells. -/
theorem portLimb_read (hk : k < 10) {i h : Nat} (hi : i < 24) (hh : h < 2) :
    (inputAt mem t ⟨k, hk⟩).portLimb i h = RowInput.limb (mem (cellAt (1 + i))).word h := by
  unfold RowInput.portLimb
  rw [ite_eq_left hh]
  split_ifs with low
  · rfl
  · show RowInput.limb (mem (cellAt (9 + (i - 8)))).word h = _
    rw [show 9 + (i - 8) = 1 + i by omega]

/-- An indirect port `offset` words above a 64-aligned base held in its base columns addresses that RAM cell. -/
theorem indirect_address {w : Nat → ZMod P} {register access : Nat} {b0 b1 : Nat} {read : Vector Nat 2}
    {write : Option (Vector Nat 2)} {base : Word} (bounded : base.Bounded) {offset : Nat}
    (room : base.lo + 4 * offset < 65536) (lo : w b0 = (base.lo : ZMod P)) (hi : w b1 = (base.hi : ZMod P)) :
    MemoryAddress.code (.indirect ⟨register, access, #v[b0, b1], 0, none, 4 * offset, read, write⟩) w =
      (ramCell base offset).addressCode := by
  have high := bounded.2
  simp only [limbBase] at high
  rw [ramCell_code bounded room]
  simp only [MemoryAddress.code, Verification.IndirectPort.rawAddress, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, lo, hi, Option.elim, Nat.cast_zero, zero_mul, add_zero]
  rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega),
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)]

/-- Each port reads its cell's current token. -/
theorem read (inv : Inv mem t k) (hk : k < 10) (j : Nat) (hj : j < 43) :
    readToken (inputAt mem t ⟨k, hk⟩).assignment (ports[j]'(by change j < 43; exact hj)) = mem (cellAt j) := by
  have clock := port_clock ⟨j, hj⟩
  have cell := cellAt_mem (j := j) hj
  have x10 : (mem (.register 10)).word.lo = 0 ∧ (mem (.register 10)).word.hi = 64 := by rw [inv.state]; exact ⟨rfl, rfl⟩
  have x11 : (mem (.register 11)).word.lo = 128 ∧ (mem (.register 11)).word.hi = 64 := by
    rw [inv.message]; exact ⟨rfl, rfl⟩
  have previous := (inputAt mem t ⟨k, hk⟩).assignment_previous (p := P) hj
  have previousHigh := (inputAt mem t ⟨k, hk⟩).assignment_previousHigh (p := P) hj
  obtain ⟨r0, w0, a0, r25, w25, a25, r42, w42, a42⟩ := port_registers
  by_cases zero : j = 0
  · subst zero
    exact read_eq (by decide) (congrArg TimestampPort.previous clock) r0
      (by rw [a0, inv.address _ cell]; rfl) previous previousHigh rfl rfl rfl (inv.high _ cell) (inv.words _ cell)
  by_cases state : j < 25
  · obtain ⟨i, rfl⟩ : ∃ i, j = 1 + i := ⟨j - 1, by omega⟩
    obtain ⟨readValue, -, address⟩ := port_state ⟨i, by omega⟩
    have target : cellAt (1 + i) = ramCell stateBase i := by
      unfold cellAt; rw [ite_eq_right (by omega), ite_eq_left (by omega), show 1 + i - 1 = i by omega]
    refine read_eq (by decide) (congrArg TimestampPort.previous clock) readValue ?_ previous previousHigh
      ((inputAt mem t ⟨k, hk⟩).assignment_portRead (h := 0) (by omega) (by omega) |>.trans ?_)
      ((inputAt mem t ⟨k, hk⟩).assignment_portRead (h := 1) (by omega) (by omega) |>.trans ?_) rfl
      (inv.high _ cell) (inv.words _ cell)
    · rw [address, inv.address _ cell, target]
      exact indirect_address (by simp [stateBase, Word.Bounded, limbBase]) (by simp only [stateBase]; omega)
        (congrArg (fun n : Nat => (n : ZMod P)) x10.1)
        (congrArg (fun n : Nat => (n : ZMod P)) x10.2)
    · rw [portLimb_read hk (by omega) (by omega)]; rfl
    · rw [portLimb_read hk (by omega) (by omega)]; rfl
  by_cases eleven : j = 25
  · subst eleven
    exact read_eq (by decide) (congrArg TimestampPort.previous clock) r25
      (by rw [a25, inv.address _ cell]; rfl) previous previousHigh rfl rfl rfl (inv.high _ cell) (inv.words _ cell)
  by_cases message : j < 42
  · obtain ⟨i, rfl⟩ : ∃ i, j = 26 + i := ⟨j - 26, by omega⟩
    obtain ⟨readValue, -, address⟩ := port_message ⟨i, by omega⟩
    have target : cellAt (26 + i) = ramCell messageBase i := by
      unfold cellAt
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show 26 + i - 26 = i by omega]
    refine read_eq (by decide) (congrArg TimestampPort.previous clock) readValue ?_ previous previousHigh
      ((inputAt mem t ⟨k, hk⟩).assignment_messageRead (h := 0) (by omega) (by omega))
      ((inputAt mem t ⟨k, hk⟩).assignment_messageRead (h := 1) (by omega) (by omega)) rfl
      (inv.high _ cell) (inv.words _ cell)
    rw [address, inv.address _ cell, target]
    exact indirect_address (by simp [messageBase, Word.Bounded, limbBase]) (by simp only [messageBase]; omega)
      (congrArg (fun n : Nat => (n : ZMod P)) x11.1) (congrArg (fun n : Nat => (n : ZMod P)) x11.2)
  obtain rfl : j = 42 := by omega
  have control := inv.control
  have small : 8 * 2 ^ k % 8192 = 8 * 2 ^ k := Nat.mod_eq_of_lt (by
    have : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    omega)
  exact read_eq (by decide) (congrArg TimestampPort.previous clock) r42
    (by rw [a42, inv.address _ cell]; rfl) previous previousHigh
    (by rw [show cellAt 42 = .register 12 from rfl, control]; rfl)
    (by rw [show cellAt 42 = .register 12 from rfl, control]; simp only [controlWord, small]; rfl) rfl
    (inv.high _ cell) (inv.words _ cell)

end Airbender.NonVacuous.Blake2RoundSpan
