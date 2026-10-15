import Airbender.Review.Circuits.Bigint.PointerABI
import Airbender.Review.Helpers.Context.ExternalBoundary.BigintABI
import Airbender.Review.Helpers.Memory.AtomicWrites

namespace Airbender.Bigint.Call
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- The selected clauses of the existing pinned bigint reference, independent
    of circuit columns. The command binds one opcode and the incoming carry. -/
def Operation (command : ExternalBoundary.BigintABI.Command)
    (left right : Vector Nat 16) (output : Bigint.Output) : Prop :=
  match command.opcode.val with
  | 0 => Additive.spec ⟨.add, left, right, command.carry⟩ output
  | 1 => Additive.spec ⟨.sub, left, right, command.carry⟩ output
  | 2 => Additive.spec ⟨.reverseSub, left, right, command.carry⟩ output
  | 3 => Multiplication.spec ⟨.low, left, right⟩ output
  | 4 => Multiplication.spec ⟨.high, left, right⟩ output
  | 5 => Equality.spec ⟨left, right⟩ output
  | _ => Additive.spec ⟨.copy, left, right, command.carry⟩ output

def word (limbs : Vector Nat 16) (i : Fin 8) : BitVec 32 :=
  (Word.mk limbs[2 * i.val] limbs[2 * i.val + 1]).toBitVec

/-- Actual little-endian RAM operand reads at the aligned public pointer.
    Canonical limb decomposition is part of the reference representation. -/
def Reads (state : State) (pointer : BitVec 32) (limbs : Vector Nat 16) : Prop :=
  (∀ i : Fin 16, limbs[i] < limbBase) ∧
    ∀ i : Fin 8, (Cell.ram (pointer + BitVec.ofNat 32 (4 * i.val))).read state =
      .ok (word limbs i) state

/-- The fixed ABI footprint, with no native-port metadata. -/
def cells (pointers : Addresses.Input) : Vector Cell 19 :=
  Vector.ofFn fun i =>
    if i.val = 0 then .register 10
    else if i.val < 9 then .ram (pointers.left.toBitVec + BitVec.ofNat 32 (4 * (i.val - 1)))
    else if i.val = 9 then .register 11
    else if i.val < 18 then .ram (pointers.right.toBitVec + BitVec.ofNat 32 (4 * (i.val - 10)))
    else .register 12

def results (pointers : Addresses.Input) (right : Vector Nat 16) (output : Bigint.Output) :
    Vector (BitVec 32) 19 :=
  Vector.ofFn fun i =>
    if zero : i.val = 0 then pointers.left.toBitVec
    else if left : i.val < 9 then word output.result ⟨i.val - 1, by omega⟩
    else if middle : i.val = 9 then pointers.right.toBitVec
    else if rightWord : i.val < 18 then word right ⟨i.val - 10, by omega⟩
    else output.control.toBitVec

def operands (pointers : Addresses.Input) (command : ExternalBoundary.BigintABI.Command)
    (left right : Vector Nat 16) : Vector (BitVec 32) 19 :=
  results pointers right ⟨left, command.word⟩

/-- One full call's architectural writes. Pointer/message refreshes are
    explicit no-ops; the only changed cells are the left block and
    x12. This list depends on reference operands/results, not native ports. -/
def writes (pointers : Addresses.Input) (right : Vector Nat 16) (output : Bigint.Output) :
    List (Cell × BitVec 32) :=
  ((cells pointers).zip (results pointers right output)).toList

/-- Complete successful custom-call state relation for the pinned project ABI.
    All pointers, controls and operand reads come from the initial Sail state;
    operation clauses determine the result, and atomic Sail writes determine
    the entire final state. No circuit witness or expected result is an input.
    Invalid calls and exceptional execution are outside this successful path. -/
def Executes (before after : State) : Prop :=
  ∃ (pointers : Addresses.Input) (command : ExternalBoundary.BigintABI.Command)
    (left right : Vector Nat 16) (output : Bigint.Output),
    Addresses.PointerABI pointers ∧
    (Cell.register 10).read before = .ok pointers.left.toBitVec before ∧
    (Cell.register 11).read before = .ok pointers.right.toBitVec before ∧
    (Cell.register 12).read before = .ok command.word.toBitVec before ∧
    Reads before pointers.left.toBitVec left ∧ Reads before pointers.right.toBitVec right ∧
    Operation command left right output ∧ AtomicWrites (writes pointers right output) before after

/-- Successful project call followed by Sail's original ordinary PC advance. -/
def Retires (before after : State) : Prop :=
  ∃ middle, Executes before middle ∧
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) middle =
      .ok () after

end Airbender.Bigint.Call
