module
public import Slop.NonVacuous.Blake2RoundSpan.Valid
public import Slop.NonVacuous.Blake2GSpan.Block
public import Slop.Blake2Round.ArtifactChecks

@[expose] public section

/-! One round row of the span, read from a memory of current tokens (`Blake2GSpan.Memory`): its 43 cells are fixed
    (x10, the 24 state words at 0x400000, x11, the 16 message words at 0x400080, x12), in port order. The row's
    inputs are the words and clocks at those cells, its round is the span position. Under the span invariant `Inv`
    (tokens at their cells, low clocks at most the invocation clock, canonical words, the two pointers and the
    round bit `3 + k` in x12) the inputs are valid. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Trace Blake2GSpan

/-- The span's state and message pointers: 0x400000 and 0x400080. -/
def stateBase : Word := ⟨0, 64⟩
def messageBase : Word := ⟨128, 64⟩

/-- The cell of port `j`. -/
def cellAt (j : Nat) : Cell :=
  if j = 0 then .register 10 else if j < 25 then ramCell stateBase (j - 1) else if j = 25 then .register 11
  else if j < 42 then ramCell messageBase (j - 26) else .register 12

/-- The span's 43 cells, in port order. -/
def cells : List Cell := (List.range 43).map cellAt

theorem cellAt_mem {j : Nat} (hj : j < 43) : cellAt j ∈ cells := List.mem_map_of_mem (List.mem_range.mpr hj)

theorem cells_nodup : cells.Nodup := by decide +kernel

/-- The control word before round `k`: round bit `3 + k` (none after the tenth round). -/
def controlWord (k : Nat) : Word := ⟨0, 8 * 2 ^ k % 8192⟩

/-- The row's inputs at round `k`: the words read at its cells, their clocks, and the invocation clock `t`. -/
def inputAt (mem : Memory) (t : Nat) (k : Fin 10) : RowInput where
  round := k
  statePointer := (mem (.register 10)).word
  messagePointer := (mem (.register 11)).word
  state i := (mem (cellAt (1 + i))).word
  extended i := (mem (cellAt (9 + i))).word
  message i := (mem (cellAt (26 + i))).word
  previous j := (mem (cellAt j)).time.1.val
  invocation := t

def rowAt' (mem : Memory) (t : Nat) (k : Fin 10) : Delegation.Row babyBearModulus :=
  ⟨.blakeRound, (inputAt mem t k).assignment⟩

/-- The row's steps: each port's cell and its write. -/
def stepsAt (mem : Memory) (t : Nat) (k : Fin 10) : List (Cell × MemoryToken babyBearModulus) :=
  cells.zip ((rowAt' mem t k).ports.toList.map (rowAt' mem t k).writeToken)

/-- The span invariant before round `k` at invocation clock `t`. -/
structure Inv (mem : Memory) (t k : Nat) : Prop where
  address : ∀ c ∈ cells, (mem c).address = c.addressCode
  high : ∀ c ∈ cells, (mem c).time.2 = 0
  time : ∀ c ∈ cells, (mem c).time.1.val ≤ t
  words : ∀ c ∈ cells, (mem c).word.Bounded
  state : (mem (.register 10)).word = stateBase
  message : (mem (.register 11)).word = messageBase
  control : (mem (.register 12)).word = controlWord k

/-- Under the invariant the row's inputs are valid. -/
theorem valid {mem : Memory} {t k : Nat} (inv : Inv mem t k) (hk : k < 10) (step : t % 4 = 1)
    (room : t + 2 < timestampBase) : (inputAt mem t ⟨k, hk⟩).Valid where
  statePointer := by
    show (mem (.register 10)).word.Bounded ∧ (mem (.register 10)).word.lo % 128 = 0
    rw [inv.state]
    simp [stateBase, Word.Bounded, limbBase]
  messagePointer := by
    show (mem (.register 11)).word.Bounded ∧ (mem (.register 11)).word.lo % 64 = 0
    rw [inv.message]
    simp [messageBase, Word.Bounded, limbBase]
  state i hi := inv.words _ (cellAt_mem (by omega))
  extended i hi := inv.words _ (cellAt_mem (by omega))
  message i hi := inv.words _ (cellAt_mem (by omega))
  previous j hj := show _ < t + 2 from Nat.lt_of_le_of_lt (inv.time _ (cellAt_mem hj)) (by omega)
  invocation := step
  room := room

end Airbender.NonVacuous.Blake2RoundSpan
