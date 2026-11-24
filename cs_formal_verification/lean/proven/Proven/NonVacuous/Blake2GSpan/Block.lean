module
public import Proven.NonVacuous.Blake2GSpan.Row
public import Proven.NonVacuous.SequentialRun
public import Human.Helpers.Delegation.Memory
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! One G row of the span, read from a memory of current tokens: the cells its ports access (the pointers in x10
    and x11, the lanes and message words the controller selects at x12), its honest inputs and assignment, and its
    steps in the sequential run. Under the span invariant `Inv` (tokens at their cells, low clocks below the next
    invocation, canonical words, the fixed pointers and an eight-bit control word) the row's inputs are valid, its
    memory steps are the run's edges, and the memory after it satisfies the invariant at the next invocation. -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic Trace

/-- The span's state and message pointers: 0x400000 and 0x400040. -/
def stateBase : Word := ⟨0, 64⟩
def messageBase : Word := ⟨64, 64⟩

/-- The RAM word `offset` words after `base`. -/
def ramCell (base : Word) (offset : Nat) : Cell := .ram (BitVec.ofNat 32 (base.value + 4 * offset))

/-- The span's 35 cells: x10, x11, x12, the sixteen state words and the sixteen message words. -/
def cells : List Cell :=
  [.register 10, .register 11, .register 12] ++ (List.range 16).map (ramCell stateBase) ++
    (List.range 16).map (ramCell messageBase)

/-- A memory: the current token of every cell. -/
abbrev Memory := Cell → MemoryToken babyBearModulus

namespace Memory
variable (mem : Memory) (t : Nat)

/-- The controller row at the memory's control word. -/
def controls : Vector Nat 7 :=
  Blake2G.Control.controllerRows ⟨256 + (mem (.register 12)).word.lo % 256, by omega⟩

/-- The cells a row accesses, in port order. -/
def ports : Vector Cell 9 :=
  #v[.register 10, ramCell (mem (.register 10)).word mem.controls[1], ramCell (mem (.register 10)).word mem.controls[2],
    ramCell (mem (.register 10)).word mem.controls[3], ramCell (mem (.register 10)).word mem.controls[4], .register 11,
    ramCell (mem (.register 11)).word mem.controls[5], ramCell (mem (.register 11)).word mem.controls[6],
    .register 12]

/-- The row's inputs: the words read at its cells, their clocks, and the invocation clock `t`. -/
def input : RowInput where
  control := (mem (.register 12)).word.lo
  statePointer := (mem (.register 10)).word
  messagePointer := (mem (.register 11)).word
  a := (mem mem.ports[1]).word
  b := (mem mem.ports[2]).word
  c := (mem mem.ports[3]).word
  d := (mem mem.ports[4]).word
  mx := (mem mem.ports[6]).word
  my := (mem mem.ports[7]).word
  previous j := (mem mem.ports[j]).time.1.val
  invocation := t

def row : Delegation.Row babyBearModulus := ⟨.blakeG, (mem.input t).assignment⟩

/-- The row's steps: each port's cell and its write. -/
def steps : List (Cell × MemoryToken babyBearModulus) :=
  mem.ports.toList.zip ((mem.row t).ports.toList.map (mem.row t).writeToken)

end Memory

/-- The span invariant before the row at invocation clock `t`. -/
structure Inv (mem : Memory) (t : Nat) : Prop where
  address : ∀ c ∈ cells, (mem c).address = c.addressCode
  high : ∀ c ∈ cells, (mem c).time.2 = 0
  time : ∀ c ∈ cells, (mem c).time.1.val ≤ t
  words : ∀ c ∈ cells, (mem c).word.Bounded
  state : (mem (.register 10)).word = stateBase
  message : (mem (.register 11)).word = messageBase
  control : (mem (.register 12)).word.hi = 0 ∧ (mem (.register 12)).word.lo < 256

/-- The controller row of an active call: an eight-bit next control word, one lane set, two message words. -/
theorem control_row (r : Nat) : ∃ (next : Nat) (m : Fin 8) (round : Fin 10), next < 256 ∧
    Blake2G.Control.controllerRows ⟨256 + r % 256, by omega⟩ = #v[next, Blake2G.Control.stateLanes[m][0],
      Blake2G.Control.stateLanes[m][1], Blake2G.Control.stateLanes[m][2], Blake2G.Control.stateLanes[m][3],
      Blake2G.Control.messageSchedule[round][2 * m.val], Blake2G.Control.messageSchedule[round][2 * m.val + 1]] := by
  have active : decide (256 ≤ 256 + r % 256) = true := by simp
  simp only [Blake2G.Control.controllerRows, Blake2G.Control.step, active, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Blake2G.Control.Output.row]
  refine ⟨_, _, _, ?_, rfl⟩
  split_ifs <;> omega

theorem lanes : ∀ m : Fin 8, [Blake2G.Control.stateLanes[m][0], Blake2G.Control.stateLanes[m][1],
    Blake2G.Control.stateLanes[m][2], Blake2G.Control.stateLanes[m][3]].Nodup ∧
      ∀ k (h : k < 4), Blake2G.Control.stateLanes[m][k] < 16 := by
  decide

theorem messages : ∀ (round : Fin 10) (m : Fin 8),
    Blake2G.Control.messageSchedule[round][2 * m.val] ≠ Blake2G.Control.messageSchedule[round][2 * m.val + 1] ∧
      Blake2G.Control.messageSchedule[round][2 * m.val] < 16 ∧
      Blake2G.Control.messageSchedule[round][2 * m.val + 1] < 16 := by
  decide

/-- The controller row's facts the span uses. -/
theorem controls_facts (mem : Memory) :
    mem.controls[0] < 256 ∧ [mem.controls[1], mem.controls[2], mem.controls[3], mem.controls[4]].Nodup ∧
      mem.controls[5] ≠ mem.controls[6] ∧ mem.controls[1] < 16 ∧ mem.controls[2] < 16 ∧ mem.controls[3] < 16 ∧
      mem.controls[4] < 16 ∧ mem.controls[5] < 16 ∧ mem.controls[6] < 16 := by
  obtain ⟨next, m, round, bound, row⟩ := control_row (mem (.register 12)).word.lo
  obtain ⟨distinct, small⟩ := lanes m
  obtain ⟨different, x, y⟩ := messages round m
  simp only [Memory.controls, row, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  exact ⟨bound, distinct, different, small 0 (by decide), small 1 (by decide), small 2 (by decide),
    small 3 (by decide), x, y⟩

/-- A RAM cell a few words above a 64-aligned base: its address limbs are the base's, the offset added to the low
    limb without carry. -/
theorem ramCell_code {base : Word} (bounded : base.Bounded) {offset : Nat} (room : base.lo + 4 * offset < 65536) :
    (ramCell base offset).addressCode = Nat.pair 1 (Nat.pair (base.lo + 4 * offset) base.hi) := by
  simp only [Word.Bounded, limbBase] at bounded
  simp only [ramCell, Cell.addressCode, Word.ofBitVec, Word.value, limbBase, BitVec.toNat_ofNat]
  congr 2 <;> omega

/-- The cells of a row, by the controller row's lane set and message words. -/
theorem ports_eq {mem : Memory} {t : Nat} (inv : Inv mem t) : ∃ (m : Fin 8) (round : Fin 10), mem.ports =
    #v[.register 10, ramCell stateBase Blake2G.Control.stateLanes[m][0],
      ramCell stateBase Blake2G.Control.stateLanes[m][1], ramCell stateBase Blake2G.Control.stateLanes[m][2],
      ramCell stateBase Blake2G.Control.stateLanes[m][3], .register 11,
      ramCell messageBase Blake2G.Control.messageSchedule[round][2 * m.val],
      ramCell messageBase Blake2G.Control.messageSchedule[round][2 * m.val + 1], .register 12] := by
  obtain ⟨next, m, round, -, row⟩ := control_row (mem (.register 12)).word.lo
  refine ⟨m, round, ?_⟩
  simp only [Memory.ports, Memory.controls, row, inv.state, inv.message, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]

/-- Every lane set and message pair gives nine different cells. -/
theorem ports_distinct : ∀ (m : Fin 8) (round : Fin 10), [Cell.register 10,
    ramCell stateBase Blake2G.Control.stateLanes[m][0], ramCell stateBase Blake2G.Control.stateLanes[m][1],
    ramCell stateBase Blake2G.Control.stateLanes[m][2], ramCell stateBase Blake2G.Control.stateLanes[m][3],
    .register 11, ramCell messageBase Blake2G.Control.messageSchedule[round][2 * m.val],
    ramCell messageBase Blake2G.Control.messageSchedule[round][2 * m.val + 1], .register 12].Nodup := by
  decide +kernel

theorem ports_nodup {mem : Memory} {t : Nat} (inv : Inv mem t) : mem.ports.toList.Nodup := by
  obtain ⟨m, round, ports⟩ := ports_eq inv
  rw [ports]
  exact ports_distinct m round

theorem ports_mem {mem : Memory} {t : Nat} (inv : Inv mem t) (j : Fin 9) : mem.ports[j] ∈ cells := by
  obtain ⟨m, round, ports⟩ := ports_eq inv
  obtain ⟨-, small⟩ := lanes m
  obtain ⟨-, x, y⟩ := messages round m
  have state (o : Nat) (h : o < 16) : ramCell stateBase o ∈ cells :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, List.mem_range.mpr h, rfl⟩))
  have message (o : Nat) (h : o < 16) : ramCell messageBase o ∈ cells :=
    List.mem_append_right _ (List.mem_map.mpr ⟨o, List.mem_range.mpr h, rfl⟩)
  rw [ports]
  obtain ⟨n, bound⟩ := j
  interval_cases n <;> simp only [Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first
    | exact state _ (small _ (by decide)) | exact message _ x | exact message _ y
    | exact List.mem_append_left _ (List.mem_append_left _ (by decide))

/-- Under the invariant the row's inputs are valid. -/
theorem valid {mem : Memory} {t : Nat} (inv : Inv mem t) (step : t % 4 = 1) (room : t + 2 < timestampBase) :
    (mem.input t).Valid where
  control := inv.control.2
  statePointer := by
    show (mem (.register 10)).word.Bounded ∧ (mem (.register 10)).word.lo % 64 = 0
    rw [inv.state]
    simp [stateBase, Word.Bounded, limbBase]
  messagePointer := by
    show (mem (.register 11)).word.Bounded ∧ (mem (.register 11)).word.lo % 64 = 0
    rw [inv.message]
    simp [messageBase, Word.Bounded, limbBase]
  a := inv.words _ (ports_mem inv 1)
  b := inv.words _ (ports_mem inv 2)
  c := inv.words _ (ports_mem inv 3)
  d := inv.words _ (ports_mem inv 4)
  mx := inv.words _ (ports_mem inv 6)
  my := inv.words _ (ports_mem inv 7)
  previous j := Nat.lt_of_le_of_lt (inv.time _ (ports_mem inv j)) (by simp only [Memory.input]; omega)
  invocation := step
  room := room

end Airbender.NonVacuous.Blake2GSpan
