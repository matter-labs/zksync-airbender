module
public import Human.Circuits.Keccak.Tables.Setup
public import Human.Circuits.Keccak.Tables.Controller
public import Human.Circuits.Keccak.ControlUpdate
public import Human.Helpers.Core.Word
public import Slop.NonVacuous.HonestAttr
public import Mathlib.Data.ZMod.Defs

@[expose] public section

/-! The honest assignment of one Keccak special5 row (`Keccak.importedConstraints`' columns, numbered as the
    artifact numbers them), computed from the row's control state, the state pointer, the six lanes read (four
    16-bit limbs each), the previous low clocks of its fourteen ports and its invocation clock. The row performs
    five binary operations (`Op`): a byte operation (XOR, Iota XOR or ANDN, table tags 4, 38, 39) over eight byte
    lookups, or a 64-bit rotation over four 16-bit rotation lookups. The mode selects their operands (lanes read
    or earlier results) and where their results go (written lanes or the three scratch values); untouched lanes
    are written back unchanged. -/

namespace Airbender.NonVacuous.KeccakSpan
open Arithmetic

/-- One binary operation: a byte operation with table tag `tag`, or (`rot`) a left rotation by `amount`, of
    the 64-bit operands `A` and `B` given as four 16-bit limbs. -/
structure Op where
  rot : Bool
  amount : Nat
  tag : Nat
  A : Nat → Nat
  B : Nat → Nat

def Op.byte (tag : Nat) (A B : Nat → Nat) : Op := ⟨false, 0, tag, A, B⟩
def Op.rotate (amount : Nat) (A : Nat → Nat) : Op := ⟨true, amount, 0, A, fun _ => 0⟩

/-- The value of a byte table at `a`, `b`: Iota XOR (38), ANDN (39) or XOR. -/
def byteOp (tag a b : Nat) : Nat :=
  if tag = 38 then a ^^^ Keccak.iotaByte b else if tag = 39 then (a ^^^ 255) &&& b else a ^^^ b

namespace Op
variable (o : Op)

/-- The rotation within a limb and the number of whole limbs rotated. -/
def shift : Nat := o.amount % 16
def limbs : Nat := o.amount / 16

/-- The eight lookups' first, second and third entries. -/
def a (i : Nat) : Nat :=
  if o.rot then (if i < 4 then o.A i + 65536 * o.shift else 0)
  else if i % 2 = 0 then o.A (i / 2) % 256 else o.A (i / 2) / 256
def b (i : Nat) : Nat :=
  if o.rot then (if i < 4 then o.A i / 2 ^ (16 - o.shift) else 0)
  else if i % 2 = 0 then o.B (i / 2) % 256 else o.B (i / 2) / 256
def c (i : Nat) : Nat :=
  if o.rot then (if i < 4 then o.A i * 2 ^ o.shift % 65536 else 0)
  else byteOp o.tag (o.a i) (o.b i)

/-- The lookups' table tag. -/
def tagValue : Nat := if o.rot then 40 else o.tag

/-- The result's four limbs. -/
def out (j : Nat) : Nat :=
  if o.rot then o.c ((j + 4 - o.limbs) % 4) + o.b ((j + 3 - o.limbs) % 4)
  else o.c (2 * j) + 256 * o.c (2 * j + 1)

/-! The entries and result of a constructed operation, for `simp only` (the operands stay atoms). They are proven by
    unfolding rather than `rfl`, so that `simp` cites them instead of leaving the kernel a definitional unfolding
    through `%` and `/` of symbolic operands (measured: seconds per use). -/

theorem byte_a (t : Nat) (A B : Nat → Nat) (i : Nat) :
    (Op.byte t A B).a i = if i % 2 = 0 then A (i / 2) % 256 else A (i / 2) / 256 := by
  rw [Op.a]; rfl
theorem byte_b (t : Nat) (A B : Nat → Nat) (i : Nat) :
    (Op.byte t A B).b i = if i % 2 = 0 then B (i / 2) % 256 else B (i / 2) / 256 := by
  rw [Op.b]; rfl
theorem byte_c (t : Nat) (A B : Nat → Nat) (i : Nat) :
    (Op.byte t A B).c i = byteOp t ((Op.byte t A B).a i) ((Op.byte t A B).b i) := by
  rw [Op.c]; rfl
theorem byte_out (t : Nat) (A B : Nat → Nat) (j : Nat) :
    (Op.byte t A B).out j = (Op.byte t A B).c (2 * j) + 256 * (Op.byte t A B).c (2 * j + 1) := by
  rw [Op.out]; rfl
theorem byte_tag (t : Nat) (A B : Nat → Nat) : (Op.byte t A B).tagValue = t := by
  rw [Op.tagValue]; rfl
theorem rotate_a (n : Nat) (A : Nat → Nat) (i : Nat) :
    (Op.rotate n A).a i = if i < 4 then A i + 65536 * (n % 16) else 0 := by
  rw [Op.a]; rfl
theorem rotate_b (n : Nat) (A : Nat → Nat) (i : Nat) :
    (Op.rotate n A).b i = if i < 4 then A i / 2 ^ (16 - n % 16) else 0 := by
  rw [Op.b]; rfl
theorem rotate_c (n : Nat) (A : Nat → Nat) (i : Nat) :
    (Op.rotate n A).c i = if i < 4 then A i * 2 ^ (n % 16) % 65536 else 0 := by
  rw [Op.c]; rfl
theorem rotate_out (n : Nat) (A : Nat → Nat) (j : Nat) :
    (Op.rotate n A).out j =
      (Op.rotate n A).c ((j + 4 - n / 16) % 4) + (Op.rotate n A).b ((j + 3 - n / 16) % 4) := by
  rw [Op.out]; rfl
theorem rotate_tag (n : Nat) (A : Nat → Nat) : (Op.rotate n A).tagValue = 40 := by
  rw [Op.tagValue]; rfl

end Op

/-- The Rho rotation amounts by iteration and lane. -/
def rhoAmount (iteration lane : Nat) : Nat :=
  (#v[#v[0, 36, 3, 41, 18], #v[1, 44, 10, 45, 2], #v[62, 6, 43, 15, 61], #v[28, 55, 25, 21, 56],
    #v[27, 20, 39, 8, 14]] : Vector (Vector Nat 5) 5)[iteration % 5][lane % 5]

/-- The Rho amounts, one fact per iteration and lane (by evaluation). -/
theorem rhoAmount_0_0 : rhoAmount 0 0 = 0 := by decide
theorem rhoAmount_0_1 : rhoAmount 0 1 = 36 := by decide
theorem rhoAmount_0_2 : rhoAmount 0 2 = 3 := by decide
theorem rhoAmount_0_3 : rhoAmount 0 3 = 41 := by decide
theorem rhoAmount_0_4 : rhoAmount 0 4 = 18 := by decide
theorem rhoAmount_1_0 : rhoAmount 1 0 = 1 := by decide
theorem rhoAmount_1_1 : rhoAmount 1 1 = 44 := by decide
theorem rhoAmount_1_2 : rhoAmount 1 2 = 10 := by decide
theorem rhoAmount_1_3 : rhoAmount 1 3 = 45 := by decide
theorem rhoAmount_1_4 : rhoAmount 1 4 = 2 := by decide
theorem rhoAmount_2_0 : rhoAmount 2 0 = 62 := by decide
theorem rhoAmount_2_1 : rhoAmount 2 1 = 6 := by decide
theorem rhoAmount_2_2 : rhoAmount 2 2 = 43 := by decide
theorem rhoAmount_2_3 : rhoAmount 2 3 = 15 := by decide
theorem rhoAmount_2_4 : rhoAmount 2 4 = 61 := by decide
theorem rhoAmount_3_0 : rhoAmount 3 0 = 28 := by decide
theorem rhoAmount_3_1 : rhoAmount 3 1 = 55 := by decide
theorem rhoAmount_3_2 : rhoAmount 3 2 = 25 := by decide
theorem rhoAmount_3_3 : rhoAmount 3 3 = 21 := by decide
theorem rhoAmount_3_4 : rhoAmount 3 4 = 56 := by decide
theorem rhoAmount_4_0 : rhoAmount 4 0 = 27 := by decide
theorem rhoAmount_4_1 : rhoAmount 4 1 = 20 := by decide
theorem rhoAmount_4_2 : rhoAmount 4 2 = 39 := by decide
theorem rhoAmount_4_3 : rhoAmount 4 3 = 8 := by decide
theorem rhoAmount_4_4 : rhoAmount 4 4 = 14 := by decide

/-- The inputs of one row: the control state read from x10, the state pointer read from x11, the six lanes'
    limbs read (`read lane limb`), the previous low clock of each port (in port order) and the invocation clock. -/
structure RowInput where
  state : Keccak.ControlState
  pointer : Word
  read : Nat → Nat → Nat
  previous : Nat → Nat
  invocation : Nat

namespace RowInput
variable (x : RowInput)

def mode : Nat := x.state.mode.val
def iteration : Nat := x.state.iteration.val
def round : Nat := x.state.round.val

/-- The controller row at the read control word (active). -/
def indices : Vector Nat 6 := Keccak.Controller.rows (Fin.ofNat 4096 (x.state.packed + 2048))

/-- The round in Iota's first iteration (zero otherwise), and the four Iota constant limbs. -/
def iotaRound : Nat := if x.iteration = 0 then x.round else 0
def iotaB (j : Nat) : Nat := (x.iotaRound + 64 * j) + 256 * (x.iotaRound + 64 * j + 32)

/-- The five operations, by mode. -/
def op0 : Op :=
  if x.mode = 0 then Op.byte 38 (x.read 0) x.iotaB
  else if x.mode = 1 then Op.rotate 1 (x.read 0)
  else if x.mode = 2 then Op.rotate 1 (x.read 1)
  else if x.mode = 3 then Op.byte 4 (x.read 0) (x.read 5)
  else if x.mode = 4 then Op.rotate (rhoAmount x.iteration 0) (x.read 0)
  else if x.mode = 5 then Op.byte 39 (x.read 0) (x.read 1)
  else Op.byte 39 (x.read 2) (x.read 0)

def op1 : Op :=
  if x.mode = 0 then Op.byte 4 x.op0.out (x.read 1)
  else if x.mode = 1 then Op.rotate 1 (x.read 2)
  else if x.mode = 2 then Op.byte 4 (x.read 4) x.op0.out
  else if x.mode = 3 then Op.byte 4 (x.read 1) (x.read 5)
  else if x.mode = 4 then Op.rotate (rhoAmount x.iteration 1) (x.read 1)
  else if x.mode = 5 then Op.byte 39 (x.read 1) (x.read 2)
  else Op.byte 4 (x.read 1) x.op0.out

def op2 : Op :=
  if x.mode = 0 then Op.byte 4 x.op1.out (x.read 2)
  else if x.mode = 1 then Op.byte 4 (x.read 0) x.op1.out
  else if x.mode = 2 then Op.rotate 1 (x.read 3)
  else if x.mode = 3 then Op.byte 4 (x.read 2) (x.read 5)
  else if x.mode = 4 then Op.rotate (rhoAmount x.iteration 2) (x.read 2)
  else if x.mode = 5 then Op.byte 4 (x.read 0) x.op1.out
  else Op.byte 39 (x.read 0) (x.read 4)

def op3 : Op :=
  if x.mode = 0 then Op.byte 4 x.op2.out (x.read 3)
  else if x.mode = 1 then Op.rotate 1 (x.read 4)
  else if x.mode = 2 then Op.byte 4 (x.read 1) x.op2.out
  else if x.mode = 3 then Op.byte 4 (x.read 3) (x.read 5)
  else if x.mode = 4 then Op.rotate (rhoAmount x.iteration 3) (x.read 3)
  else if x.mode = 5 then Op.byte 39 (x.read 2) (x.read 3)
  else Op.byte 4 (x.read 2) x.op2.out

def op4 : Op :=
  if x.mode = 0 then Op.byte 4 x.op3.out (x.read 4)
  else if x.mode = 1 then Op.byte 4 (x.read 2) x.op3.out
  else if x.mode = 2 then Op.byte 4 (x.read 3) (x.read 5)
  else if x.mode = 3 then Op.byte 4 (x.read 4) (x.read 5)
  else if x.mode = 4 then Op.rotate (rhoAmount x.iteration 4) (x.read 4)
  else if x.mode = 5 then Op.byte 4 (x.read 1) x.op3.out
  else Op.byte 4 (x.read 0) (x.read 3)

def op (k : Nat) : Op :=
  match k with
  | 0 => x.op0
  | 1 => x.op1
  | 2 => x.op2
  | 3 => x.op3
  | _ => x.op4

/-- The three scratch values' limbs (`temp t limb`). -/
def temp (t : Nat) : Nat → Nat :=
  if x.mode = 0 then (if t = 0 then x.op1.out else if t = 1 then x.op2.out else if t = 2 then x.op3.out else 0)
  else if x.mode = 1 then (if t = 0 then x.op1.out else if t = 1 then x.op3.out else 0)
  else if x.mode = 2 then (if t = 0 then x.op0.out else if t = 1 then x.op2.out else 0)
  else if x.mode = 5 then (if t = 0 then x.op1.out else if t = 1 then x.op3.out else 0)
  else if x.mode = 6 then (if t = 0 then x.op0.out else if t = 1 then x.op2.out else 0)
  else 0

/-- The six lanes' written limbs (`written lane limb`). -/
def written (lane : Nat) : Nat → Nat :=
  if x.mode = 0 then (if lane = 0 then x.op0.out else if lane = 5 then x.op4.out else x.read lane)
  else if x.mode = 1 then
    (if lane = 0 then x.op2.out else if lane = 2 then x.op4.out else if lane = 5 then x.op0.out else x.read lane)
  else if x.mode = 2 then
    (if lane = 1 then x.op3.out else if lane = 3 then x.op4.out else if lane = 4 then x.op1.out else x.read lane)
  else if x.mode = 3 ∨ x.mode = 4 then
    (if lane = 0 then x.op0.out else if lane = 1 then x.op1.out else if lane = 2 then x.op2.out
      else if lane = 3 then x.op3.out else if lane = 4 then x.op4.out else x.read lane)
  else if x.mode = 5 then
    (if lane = 0 then x.op2.out else if lane = 1 then x.op4.out else if lane = 4 then x.op0.out
      else if lane = 5 then x.read 0 else x.read lane)
  else (if lane = 0 then x.op4.out else if lane = 1 then x.op1.out else if lane = 2 then x.op3.out else x.read lane)

/-- A lane port column `15 + 8 lane + offset`: read low, read high, written low, written high of the lane's low
    word, then of its high word. -/
def lanePort (lane offset : Nat) : Nat :=
  match offset with
  | 0 => x.read lane 0
  | 1 => x.read lane 1
  | 2 => x.written lane 0
  | 3 => x.written lane 1
  | 4 => x.read lane 2
  | 5 => x.read lane 3
  | 6 => x.written lane 2
  | _ => x.written lane 3

/-- An operation column `102 + 24 k + offset`: the eight first, second and third lookup entries. -/
def opColumn (k offset : Nat) : Nat :=
  if offset < 8 then (x.op k).a offset
  else if offset < 16 then (x.op k).b (offset - 8)
  else (x.op k).c (offset - 16)

/-- Columns 63 to 101: the mode, iteration and round flags, Rho's iteration flags, the Iota round and constant
    limbs, and the scratch values. -/
def control (n : Nat) : Nat :=
  if n < 70 then (if x.mode = n - 63 then 1 else 0)
  else if n < 75 then (if x.iteration = n - 70 then 1 else 0)
  else if n < 80 then x.round / 2 ^ (n - 75) % 2
  else if n < 85 then (if x.mode = 4 ∧ x.iteration = n - 80 then 1 else 0)
  else if n = 85 then x.iotaRound
  else if n < 90 then x.iotaB (n - 86)
  else x.temp ((n - 90) / 4) ((n - 90) % 4)

/-- The honest value of every column. -/
def column (n : Nat) : Nat :=
  if n < 15 then
    match n with
    | 0 => 1
    | 1 => x.invocation
    | 3 => x.state.packed
    | 5 => x.state.nextPacked
    | 7 => x.indices[0]
    | 8 => x.indices[1]
    | 9 => x.indices[2]
    | 10 => x.indices[3]
    | 11 => x.indices[4]
    | 12 => x.indices[5]
    | 13 => x.pointer.lo
    | 14 => x.pointer.hi
    | _ => 0
  else if n < 63 then x.lanePort ((n - 15) / 8) ((n - 15) % 8)
  else if n < 102 then x.control n
  else if n < 222 then x.opColumn ((n - 102) / 24) ((n - 102) % 24)
  else if n < 264 then
    (if (n - 222) % 3 = 0 then x.previous ((n - 222) / 3) else if (n - 222) % 3 = 1 then 0 else 1)
  else 0

end RowInput

/-- The row's assignment over the field. -/
def RowInput.assignment {p : Nat} (x : RowInput) (i : Nat) : ZMod p := (x.column i : ZMod p)


namespace RowInput
variable {p : Nat} (x : RowInput)

/-! The honest value of each column, by `rfl` (one lemma per column, for `simp only [honest_column]`); the clock
    columns 222 to 263 are cited by their general form (`clock_low`, `clock_high`, `clock_borrow`). -/

@[honest_column] theorem assignment_0 : x.assignment (p := p) 0 = ((1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_1 : x.assignment (p := p) 1 = ((x.invocation : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_2 : x.assignment (p := p) 2 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_3 : x.assignment (p := p) 3 = ((x.state.packed : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_4 : x.assignment (p := p) 4 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_5 : x.assignment (p := p) 5 = ((x.state.nextPacked : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_6 : x.assignment (p := p) 6 = ((0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_7 : x.assignment (p := p) 7 = ((x.indices[0] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_8 : x.assignment (p := p) 8 = ((x.indices[1] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_9 : x.assignment (p := p) 9 = ((x.indices[2] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_10 : x.assignment (p := p) 10 = ((x.indices[3] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_11 : x.assignment (p := p) 11 = ((x.indices[4] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_12 : x.assignment (p := p) 12 = ((x.indices[5] : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_13 : x.assignment (p := p) 13 = ((x.pointer.lo : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_14 : x.assignment (p := p) 14 = ((x.pointer.hi : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_15 : x.assignment (p := p) 15 = ((x.read 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_16 : x.assignment (p := p) 16 = ((x.read 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_17 : x.assignment (p := p) 17 = ((x.written 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_18 : x.assignment (p := p) 18 = ((x.written 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_19 : x.assignment (p := p) 19 = ((x.read 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_20 : x.assignment (p := p) 20 = ((x.read 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_21 : x.assignment (p := p) 21 = ((x.written 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_22 : x.assignment (p := p) 22 = ((x.written 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_23 : x.assignment (p := p) 23 = ((x.read 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_24 : x.assignment (p := p) 24 = ((x.read 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_25 : x.assignment (p := p) 25 = ((x.written 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_26 : x.assignment (p := p) 26 = ((x.written 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_27 : x.assignment (p := p) 27 = ((x.read 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_28 : x.assignment (p := p) 28 = ((x.read 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_29 : x.assignment (p := p) 29 = ((x.written 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_30 : x.assignment (p := p) 30 = ((x.written 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_31 : x.assignment (p := p) 31 = ((x.read 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_32 : x.assignment (p := p) 32 = ((x.read 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_33 : x.assignment (p := p) 33 = ((x.written 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_34 : x.assignment (p := p) 34 = ((x.written 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_35 : x.assignment (p := p) 35 = ((x.read 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_36 : x.assignment (p := p) 36 = ((x.read 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_37 : x.assignment (p := p) 37 = ((x.written 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_38 : x.assignment (p := p) 38 = ((x.written 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_39 : x.assignment (p := p) 39 = ((x.read 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_40 : x.assignment (p := p) 40 = ((x.read 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_41 : x.assignment (p := p) 41 = ((x.written 3 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_42 : x.assignment (p := p) 42 = ((x.written 3 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_43 : x.assignment (p := p) 43 = ((x.read 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_44 : x.assignment (p := p) 44 = ((x.read 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_45 : x.assignment (p := p) 45 = ((x.written 3 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_46 : x.assignment (p := p) 46 = ((x.written 3 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_47 : x.assignment (p := p) 47 = ((x.read 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_48 : x.assignment (p := p) 48 = ((x.read 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_49 : x.assignment (p := p) 49 = ((x.written 4 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_50 : x.assignment (p := p) 50 = ((x.written 4 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_51 : x.assignment (p := p) 51 = ((x.read 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_52 : x.assignment (p := p) 52 = ((x.read 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_53 : x.assignment (p := p) 53 = ((x.written 4 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_54 : x.assignment (p := p) 54 = ((x.written 4 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_55 : x.assignment (p := p) 55 = ((x.read 5 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_56 : x.assignment (p := p) 56 = ((x.read 5 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_57 : x.assignment (p := p) 57 = ((x.written 5 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_58 : x.assignment (p := p) 58 = ((x.written 5 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_59 : x.assignment (p := p) 59 = ((x.read 5 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_60 : x.assignment (p := p) 60 = ((x.read 5 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_61 : x.assignment (p := p) 61 = ((x.written 5 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_62 : x.assignment (p := p) 62 = ((x.written 5 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_63 :
    x.assignment (p := p) 63 = ((if x.mode = 0 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_64 :
    x.assignment (p := p) 64 = ((if x.mode = 1 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_65 :
    x.assignment (p := p) 65 = ((if x.mode = 2 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_66 :
    x.assignment (p := p) 66 = ((if x.mode = 3 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_67 :
    x.assignment (p := p) 67 = ((if x.mode = 4 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_68 :
    x.assignment (p := p) 68 = ((if x.mode = 5 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_69 :
    x.assignment (p := p) 69 = ((if x.mode = 6 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_70 :
    x.assignment (p := p) 70 = ((if x.iteration = 0 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_71 :
    x.assignment (p := p) 71 = ((if x.iteration = 1 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_72 :
    x.assignment (p := p) 72 = ((if x.iteration = 2 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_73 :
    x.assignment (p := p) 73 = ((if x.iteration = 3 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_74 :
    x.assignment (p := p) 74 = ((if x.iteration = 4 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_75 : x.assignment (p := p) 75 = ((x.round / 2 ^ 0 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_76 : x.assignment (p := p) 76 = ((x.round / 2 ^ 1 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_77 : x.assignment (p := p) 77 = ((x.round / 2 ^ 2 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_78 : x.assignment (p := p) 78 = ((x.round / 2 ^ 3 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_79 : x.assignment (p := p) 79 = ((x.round / 2 ^ 4 % 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_80 :
    x.assignment (p := p) 80 = ((if x.mode = 4 ∧ x.iteration = 0 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_81 :
    x.assignment (p := p) 81 = ((if x.mode = 4 ∧ x.iteration = 1 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_82 :
    x.assignment (p := p) 82 = ((if x.mode = 4 ∧ x.iteration = 2 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_83 :
    x.assignment (p := p) 83 = ((if x.mode = 4 ∧ x.iteration = 3 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_84 :
    x.assignment (p := p) 84 = ((if x.mode = 4 ∧ x.iteration = 4 then 1 else 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_85 : x.assignment (p := p) 85 = ((x.iotaRound : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_86 : x.assignment (p := p) 86 = ((x.iotaB 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_87 : x.assignment (p := p) 87 = ((x.iotaB 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_88 : x.assignment (p := p) 88 = ((x.iotaB 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_89 : x.assignment (p := p) 89 = ((x.iotaB 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_90 : x.assignment (p := p) 90 = ((x.temp 0 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_91 : x.assignment (p := p) 91 = ((x.temp 0 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_92 : x.assignment (p := p) 92 = ((x.temp 0 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_93 : x.assignment (p := p) 93 = ((x.temp 0 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_94 : x.assignment (p := p) 94 = ((x.temp 1 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_95 : x.assignment (p := p) 95 = ((x.temp 1 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_96 : x.assignment (p := p) 96 = ((x.temp 1 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_97 : x.assignment (p := p) 97 = ((x.temp 1 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_98 : x.assignment (p := p) 98 = ((x.temp 2 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_99 : x.assignment (p := p) 99 = ((x.temp 2 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_100 : x.assignment (p := p) 100 = ((x.temp 2 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_101 : x.assignment (p := p) 101 = ((x.temp 2 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_102 : x.assignment (p := p) 102 = ((x.op0.a 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_103 : x.assignment (p := p) 103 = ((x.op0.a 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_104 : x.assignment (p := p) 104 = ((x.op0.a 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_105 : x.assignment (p := p) 105 = ((x.op0.a 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_106 : x.assignment (p := p) 106 = ((x.op0.a 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_107 : x.assignment (p := p) 107 = ((x.op0.a 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_108 : x.assignment (p := p) 108 = ((x.op0.a 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_109 : x.assignment (p := p) 109 = ((x.op0.a 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_110 : x.assignment (p := p) 110 = ((x.op0.b 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_111 : x.assignment (p := p) 111 = ((x.op0.b 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_112 : x.assignment (p := p) 112 = ((x.op0.b 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_113 : x.assignment (p := p) 113 = ((x.op0.b 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_114 : x.assignment (p := p) 114 = ((x.op0.b 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_115 : x.assignment (p := p) 115 = ((x.op0.b 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_116 : x.assignment (p := p) 116 = ((x.op0.b 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_117 : x.assignment (p := p) 117 = ((x.op0.b 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_118 : x.assignment (p := p) 118 = ((x.op0.c 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_119 : x.assignment (p := p) 119 = ((x.op0.c 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_120 : x.assignment (p := p) 120 = ((x.op0.c 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_121 : x.assignment (p := p) 121 = ((x.op0.c 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_122 : x.assignment (p := p) 122 = ((x.op0.c 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_123 : x.assignment (p := p) 123 = ((x.op0.c 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_124 : x.assignment (p := p) 124 = ((x.op0.c 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_125 : x.assignment (p := p) 125 = ((x.op0.c 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_126 : x.assignment (p := p) 126 = ((x.op1.a 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_127 : x.assignment (p := p) 127 = ((x.op1.a 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_128 : x.assignment (p := p) 128 = ((x.op1.a 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_129 : x.assignment (p := p) 129 = ((x.op1.a 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_130 : x.assignment (p := p) 130 = ((x.op1.a 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_131 : x.assignment (p := p) 131 = ((x.op1.a 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_132 : x.assignment (p := p) 132 = ((x.op1.a 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_133 : x.assignment (p := p) 133 = ((x.op1.a 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_134 : x.assignment (p := p) 134 = ((x.op1.b 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_135 : x.assignment (p := p) 135 = ((x.op1.b 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_136 : x.assignment (p := p) 136 = ((x.op1.b 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_137 : x.assignment (p := p) 137 = ((x.op1.b 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_138 : x.assignment (p := p) 138 = ((x.op1.b 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_139 : x.assignment (p := p) 139 = ((x.op1.b 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_140 : x.assignment (p := p) 140 = ((x.op1.b 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_141 : x.assignment (p := p) 141 = ((x.op1.b 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_142 : x.assignment (p := p) 142 = ((x.op1.c 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_143 : x.assignment (p := p) 143 = ((x.op1.c 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_144 : x.assignment (p := p) 144 = ((x.op1.c 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_145 : x.assignment (p := p) 145 = ((x.op1.c 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_146 : x.assignment (p := p) 146 = ((x.op1.c 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_147 : x.assignment (p := p) 147 = ((x.op1.c 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_148 : x.assignment (p := p) 148 = ((x.op1.c 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_149 : x.assignment (p := p) 149 = ((x.op1.c 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_150 : x.assignment (p := p) 150 = ((x.op2.a 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_151 : x.assignment (p := p) 151 = ((x.op2.a 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_152 : x.assignment (p := p) 152 = ((x.op2.a 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_153 : x.assignment (p := p) 153 = ((x.op2.a 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_154 : x.assignment (p := p) 154 = ((x.op2.a 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_155 : x.assignment (p := p) 155 = ((x.op2.a 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_156 : x.assignment (p := p) 156 = ((x.op2.a 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_157 : x.assignment (p := p) 157 = ((x.op2.a 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_158 : x.assignment (p := p) 158 = ((x.op2.b 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_159 : x.assignment (p := p) 159 = ((x.op2.b 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_160 : x.assignment (p := p) 160 = ((x.op2.b 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_161 : x.assignment (p := p) 161 = ((x.op2.b 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_162 : x.assignment (p := p) 162 = ((x.op2.b 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_163 : x.assignment (p := p) 163 = ((x.op2.b 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_164 : x.assignment (p := p) 164 = ((x.op2.b 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_165 : x.assignment (p := p) 165 = ((x.op2.b 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_166 : x.assignment (p := p) 166 = ((x.op2.c 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_167 : x.assignment (p := p) 167 = ((x.op2.c 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_168 : x.assignment (p := p) 168 = ((x.op2.c 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_169 : x.assignment (p := p) 169 = ((x.op2.c 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_170 : x.assignment (p := p) 170 = ((x.op2.c 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_171 : x.assignment (p := p) 171 = ((x.op2.c 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_172 : x.assignment (p := p) 172 = ((x.op2.c 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_173 : x.assignment (p := p) 173 = ((x.op2.c 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_174 : x.assignment (p := p) 174 = ((x.op3.a 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_175 : x.assignment (p := p) 175 = ((x.op3.a 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_176 : x.assignment (p := p) 176 = ((x.op3.a 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_177 : x.assignment (p := p) 177 = ((x.op3.a 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_178 : x.assignment (p := p) 178 = ((x.op3.a 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_179 : x.assignment (p := p) 179 = ((x.op3.a 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_180 : x.assignment (p := p) 180 = ((x.op3.a 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_181 : x.assignment (p := p) 181 = ((x.op3.a 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_182 : x.assignment (p := p) 182 = ((x.op3.b 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_183 : x.assignment (p := p) 183 = ((x.op3.b 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_184 : x.assignment (p := p) 184 = ((x.op3.b 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_185 : x.assignment (p := p) 185 = ((x.op3.b 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_186 : x.assignment (p := p) 186 = ((x.op3.b 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_187 : x.assignment (p := p) 187 = ((x.op3.b 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_188 : x.assignment (p := p) 188 = ((x.op3.b 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_189 : x.assignment (p := p) 189 = ((x.op3.b 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_190 : x.assignment (p := p) 190 = ((x.op3.c 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_191 : x.assignment (p := p) 191 = ((x.op3.c 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_192 : x.assignment (p := p) 192 = ((x.op3.c 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_193 : x.assignment (p := p) 193 = ((x.op3.c 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_194 : x.assignment (p := p) 194 = ((x.op3.c 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_195 : x.assignment (p := p) 195 = ((x.op3.c 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_196 : x.assignment (p := p) 196 = ((x.op3.c 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_197 : x.assignment (p := p) 197 = ((x.op3.c 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_198 : x.assignment (p := p) 198 = ((x.op4.a 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_199 : x.assignment (p := p) 199 = ((x.op4.a 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_200 : x.assignment (p := p) 200 = ((x.op4.a 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_201 : x.assignment (p := p) 201 = ((x.op4.a 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_202 : x.assignment (p := p) 202 = ((x.op4.a 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_203 : x.assignment (p := p) 203 = ((x.op4.a 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_204 : x.assignment (p := p) 204 = ((x.op4.a 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_205 : x.assignment (p := p) 205 = ((x.op4.a 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_206 : x.assignment (p := p) 206 = ((x.op4.b 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_207 : x.assignment (p := p) 207 = ((x.op4.b 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_208 : x.assignment (p := p) 208 = ((x.op4.b 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_209 : x.assignment (p := p) 209 = ((x.op4.b 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_210 : x.assignment (p := p) 210 = ((x.op4.b 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_211 : x.assignment (p := p) 211 = ((x.op4.b 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_212 : x.assignment (p := p) 212 = ((x.op4.b 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_213 : x.assignment (p := p) 213 = ((x.op4.b 7 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_214 : x.assignment (p := p) 214 = ((x.op4.c 0 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_215 : x.assignment (p := p) 215 = ((x.op4.c 1 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_216 : x.assignment (p := p) 216 = ((x.op4.c 2 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_217 : x.assignment (p := p) 217 = ((x.op4.c 3 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_218 : x.assignment (p := p) 218 = ((x.op4.c 4 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_219 : x.assignment (p := p) 219 = ((x.op4.c 5 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_220 : x.assignment (p := p) 220 = ((x.op4.c 6 : Nat) : ZMod p) := rfl
@[honest_column] theorem assignment_221 : x.assignment (p := p) 221 = ((x.op4.c 7 : Nat) : ZMod p) := rfl

end RowInput

end Airbender.NonVacuous.KeccakSpan
