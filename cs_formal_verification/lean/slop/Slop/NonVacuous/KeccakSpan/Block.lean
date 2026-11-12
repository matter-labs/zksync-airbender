module
public import Slop.NonVacuous.KeccakSpan.Valid
public import Slop.Keccak.PhaseSteps
public import Slop.Keccak.ControllerLayout
public import Human.Helpers.Delegation.Memory
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! Call `k` of the special5 span, read from a memory of current tokens: its control state (the pinned schedule,
    `scheduleControl`), the lanes the modeled controller selects, the cells its fourteen ports access (x10, x11 and
    the low and high word of each selected lane at the state pointer 0x400000), and its honest inputs. Under the
    span invariant `Inv` (tokens at their cells, low clocks below the invocation, canonical words, the pointer in
    x11 and the scheduled control word in x10) the inputs are valid, and the ports access fourteen distinct cells
    of the span. -/

namespace Airbender.NonVacuous.KeccakSpan
open Arithmetic Trace

/-- The state pointer 0x400000. -/
def stateBase : Word := ⟨0, 64⟩

/-- The RAM word `offset` words after the state pointer (lane `l`'s words are `2 l` and `2 l + 1`). -/
def ramCell (offset : Nat) : Cell := .ram (BitVec.ofNat 32 (stateBase.value + 4 * offset))

/-- The span's 64 cells: x10, x11 and the 31 lanes' 62 words (25 state lanes, 6 scratch lanes). -/
def cells : List Cell := [.register 10, .register 11] ++ (List.range 62).map ramCell

/-- The control state of call `k`. -/
def control (k : Nat) : Keccak.ControlState := Keccak.scheduleControl (Fin.ofNat 650 k)

/-- The lanes the controller selects for call `k`. -/
def lanes (k : Nat) : Vector Nat 6 := Keccak.Controller.rows (Fin.ofNat 4096 ((control k).packed + 2048))

/-- The cell of port `n` of call `k`. -/
def portCell (k n : Nat) : Cell :=
  if n = 0 then .register 10 else if n = 1 then .register 11
  else ramCell (2 * (lanes k)[(n - 2) / 2 % 6]'(Nat.mod_lt _ (by decide)) + (n - 2) % 2)

/-- A memory: the current token of every cell. -/
abbrev Memory := Cell → MemoryToken babyBearModulus

namespace Memory
variable (mem : Memory) (k t : Nat)

/-- The inputs of call `k` at invocation clock `t`: the lanes' limbs read at its port cells, their clocks. -/
def input : RowInput where
  state := control k
  pointer := (mem (.register 11)).word
  read lane j := if j % 2 = 0 then (mem (portCell k (2 + 2 * lane + j / 2))).word.lo
    else (mem (portCell k (2 + 2 * lane + j / 2))).word.hi
  previous n := (mem (portCell k n)).time.1.val
  invocation := t

def row : Delegation.Row babyBearModulus := ⟨.keccak, (mem.input k t).assignment⟩

/-- The row's steps: each port's cell and its write. -/
def steps : List (Cell × MemoryToken babyBearModulus) :=
  ((List.range 14).map (portCell k)).zip ((mem.row k t).ports.toList.map (mem.row k t).writeToken)

end Memory

/-- The span invariant before call `k`, at invocation clock `1 + 4 k`. -/
structure Inv (mem : Memory) (k : Nat) : Prop where
  address : ∀ c ∈ cells, (mem c).address = c.addressCode
  high : ∀ c ∈ cells, (mem c).time.2 = 0
  time : ∀ c ∈ cells, (mem c).time.1.val ≤ 1 + 4 * k
  words : ∀ c ∈ cells, (mem c).word.Bounded
  pointer : (mem (.register 11)).word = stateBase
  control : (mem (.register 10)).word = ⟨(control k).packed, 0⟩

theorem control_eq {k : Nat} (small : k < 650) : control k = Keccak.scheduleControl ⟨k, small⟩ :=
  congrArg _ (Fin.ext (Nat.mod_eq_of_lt small))

theorem lanes_bound (k : Nat) (j : Fin 6) : (lanes k)[j] < 31 := Keccak.Controller.Proofs.rows_bound _ j

theorem ramCell_mem {o : Nat} (small : o < 62) : ramCell o ∈ cells :=
  List.mem_append_right _ (List.mem_map.mpr ⟨o, List.mem_range.mpr small, rfl⟩)

theorem portCell_mem (k n : Nat) : portCell k n ∈ cells := by
  unfold portCell
  split_ifs
  · exact List.mem_append_left _ (by decide)
  · exact List.mem_append_left _ (by decide)
  · have := lanes_bound k ⟨(n - 2) / 2 % 6, Nat.mod_lt _ (by decide)⟩
    exact ramCell_mem (by simp only [Fin.getElem_fin] at this; omega)

/-- The Mix calls' lanes are the six scratch lanes, all different. -/
private theorem mix_nodup : ∀ round : Fin 24,
    (Keccak.Controller.rows (Fin.ofNat 4096
      ((Keccak.ControlState.mk 1 0 ⟨round.val, by omega⟩).packed + 2048))).toList.Nodup ∧
    (Keccak.Controller.rows (Fin.ofNat 4096
      ((Keccak.ControlState.mk 2 0 ⟨round.val, by omega⟩).packed + 2048))).toList.Nodup := by
  decide +kernel

/-- The lanes of every call of the span are six different lanes. -/
theorem lanes_nodup {k : Nat} (small : k < 649) : (lanes k).toList.Nodup := by
  have same : lanes k = Keccak.Proofs.slotIndices ⟨k, small⟩ := by
    simp only [lanes, Keccak.Proofs.slotIndices, control_eq (Nat.lt_succ_of_lt small)]
  rw [same]
  have stage : k % 27 < 27 := Nat.mod_lt _ (by decide)
  have shape : k = 27 * (k / 27) + k % 27 := (Nat.div_add_mod k 27).symm
  generalize k % 27 = s at stage shape
  generalize k / 27 = r at shape
  subst shape
  interval_cases s
  · exact Keccak.Proofs.iota_nodup (call := ⟨27 * r + 0, small⟩) (round := r) (column := 0) rfl (by decide)
  · exact Keccak.Proofs.iota_nodup (call := ⟨27 * r + 1, small⟩) (round := r) (column := 1) rfl (by decide)
  · exact Keccak.Proofs.iota_nodup (call := ⟨27 * r + 2, small⟩) (round := r) (column := 2) rfl (by decide)
  · exact Keccak.Proofs.iota_nodup (call := ⟨27 * r + 3, small⟩) (round := r) (column := 3) rfl (by decide)
  · exact Keccak.Proofs.iota_nodup (call := ⟨27 * r + 4, small⟩) (round := r) (column := 4) rfl (by decide)
  · rw [Keccak.Proofs.slotIndices, Keccak.Proofs.schedule_control_at (call := ⟨27 * r + 5, small⟩) (round := r)
      (stage := 5) rfl (by decide) (mode := 1) (iteration := 0) (by decide) (by decide)]
    exact (mix_nodup ⟨r, by omega⟩).1
  · rw [Keccak.Proofs.slotIndices, Keccak.Proofs.schedule_control_at (call := ⟨27 * r + 6, small⟩) (round := r)
      (stage := 6) rfl (by decide) (mode := 2) (iteration := 0) (by decide) (by decide)]
    exact (mix_nodup ⟨r, by omega⟩).2
  · exact Keccak.Proofs.theta_nodup (call := ⟨27 * r + 7, small⟩) (round := r) (column := 0)
      (show 27 * r + 7 = 27 * r + 7 + 0 by omega) (by decide)
  · exact Keccak.Proofs.theta_nodup (call := ⟨27 * r + 8, small⟩) (round := r) (column := 1)
      (show 27 * r + 8 = 27 * r + 7 + 1 by omega) (by decide)
  · exact Keccak.Proofs.theta_nodup (call := ⟨27 * r + 9, small⟩) (round := r) (column := 2)
      (show 27 * r + 9 = 27 * r + 7 + 2 by omega) (by decide)
  · exact Keccak.Proofs.theta_nodup (call := ⟨27 * r + 10, small⟩) (round := r) (column := 3)
      (show 27 * r + 10 = 27 * r + 7 + 3 by omega) (by decide)
  · exact Keccak.Proofs.theta_nodup (call := ⟨27 * r + 11, small⟩) (round := r) (column := 4)
      (show 27 * r + 11 = 27 * r + 7 + 4 by omega) (by decide)
  · exact Keccak.Proofs.rho_nodup (call := ⟨27 * r + 12, small⟩) (round := r) (column := 0)
      (show 27 * r + 12 = 27 * r + 12 + 0 by omega) (by decide)
  · exact Keccak.Proofs.rho_nodup (call := ⟨27 * r + 13, small⟩) (round := r) (column := 1)
      (show 27 * r + 13 = 27 * r + 12 + 1 by omega) (by decide)
  · exact Keccak.Proofs.rho_nodup (call := ⟨27 * r + 14, small⟩) (round := r) (column := 2)
      (show 27 * r + 14 = 27 * r + 12 + 2 by omega) (by decide)
  · exact Keccak.Proofs.rho_nodup (call := ⟨27 * r + 15, small⟩) (round := r) (column := 3)
      (show 27 * r + 15 = 27 * r + 12 + 3 by omega) (by decide)
  · exact Keccak.Proofs.rho_nodup (call := ⟨27 * r + 16, small⟩) (round := r) (column := 4)
      (show 27 * r + 16 = 27 * r + 12 + 4 by omega) (by decide)
  · exact Keccak.Proofs.chi_first_nodup (call := ⟨27 * r + 17, small⟩) (round := r) (row := 0)
      (show 27 * r + 17 = 27 * r + 17 + 2 * 0 by omega)
  · exact Keccak.Proofs.chi_second_nodup (call := ⟨27 * r + 18, small⟩) (round := r) (row := 0)
      (show 27 * r + 18 = 27 * r + 18 + 2 * 0 by omega)
  · exact Keccak.Proofs.chi_first_nodup (call := ⟨27 * r + 19, small⟩) (round := r) (row := 1)
      (show 27 * r + 19 = 27 * r + 17 + 2 * 1 by omega)
  · exact Keccak.Proofs.chi_second_nodup (call := ⟨27 * r + 20, small⟩) (round := r) (row := 1)
      (show 27 * r + 20 = 27 * r + 18 + 2 * 1 by omega)
  · exact Keccak.Proofs.chi_first_nodup (call := ⟨27 * r + 21, small⟩) (round := r) (row := 2)
      (show 27 * r + 21 = 27 * r + 17 + 2 * 2 by omega)
  · exact Keccak.Proofs.chi_second_nodup (call := ⟨27 * r + 22, small⟩) (round := r) (row := 2)
      (show 27 * r + 22 = 27 * r + 18 + 2 * 2 by omega)
  · exact Keccak.Proofs.chi_first_nodup (call := ⟨27 * r + 23, small⟩) (round := r) (row := 3)
      (show 27 * r + 23 = 27 * r + 17 + 2 * 3 by omega)
  · exact Keccak.Proofs.chi_second_nodup (call := ⟨27 * r + 24, small⟩) (round := r) (row := 3)
      (show 27 * r + 24 = 27 * r + 18 + 2 * 3 by omega)
  · exact Keccak.Proofs.chi_first_nodup (call := ⟨27 * r + 25, small⟩) (round := r) (row := 4)
      (show 27 * r + 25 = 27 * r + 17 + 2 * 4 by omega)
  · exact Keccak.Proofs.chi_second_nodup (call := ⟨27 * r + 26, small⟩) (round := r) (row := 4)
      (show 27 * r + 26 = 27 * r + 18 + 2 * 4 by omega)

end Airbender.NonVacuous.KeccakSpan
