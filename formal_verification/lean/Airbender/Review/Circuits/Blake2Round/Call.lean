import Airbender.Review.Circuits.Blake2Round.Row
import Airbender.Review.Helpers.Memory.AtomicWrites
import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Blake2Round.Call
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

def flags (input : Row.Input) : Nat :=
  input.reducedRounds.toNat + 2 * input.inputIsRight.toNat + 4 * input.compression.toNat

/-- Successful round arguments in the existing complete public protocol.
    Controller/round/mode agreement and the pointer ABI are properties to derive
    from that protocol and initialized history, not assumed operation results. -/
structure ABI (input : Row.Input) : Prop where
  controller : input.controller = ⟨0, flags input + 8 * 2 ^ input.round.val⟩
  round : input.round.val < if input.reducedRounds then 7 else 10
  ram : ROM.limit ≤ input.statePointer.toBitVec.toNat ∧ ROM.limit ≤ input.messagePointer.toBitVec.toNat
  aligned : input.statePointer.toBitVec.toNat % 128 = 0 ∧ input.messagePointer.toBitVec.toNat % 64 = 0
  distinct : input.statePointer.toBitVec ≠ input.messagePointer.toBitVec

def InputBounded (input : Row.Input) : Prop :=
  input.controller.Bounded ∧ input.statePointer.Bounded ∧ input.messagePointer.Bounded ∧
    (∀ i : Fin 8, input.state[i].Bounded) ∧ (∀ i : Fin 16, input.extended[i].Bounded) ∧
    (∀ i : Fin 16, input.message[i].Bounded)

def OutputBounded (output : Row.Output) : Prop :=
  output.controller.Bounded ∧ (∀ i : Fin 8, output.state[i].Bounded) ∧
    (∀ i : Fin 16, output.extended[i].Bounded)

def stateWord (state : Vector Word 8) (extended : Vector Word 16) (i : Fin 24) : Word :=
  if first : i.val < 8 then state[i.val]'first
  else extended[i.val - 8]'(by omega)

def cells (input : Row.Input) : Vector Cell 43 :=
  Vector.ofFn fun i =>
    if i.val = 0 then .register 10
    else if i.val < 25 then .ram (input.statePointer.toBitVec + BitVec.ofNat 32 (4 * (i.val - 1)))
    else if i.val = 25 then .register 11
    else if i.val < 42 then .ram (input.messagePointer.toBitVec + BitVec.ofNat 32 (4 * (i.val - 26)))
    else .register 12

def values (statePointer messagePointer : Word) (state : Vector Word 8) (extended message : Vector Word 16)
    (controller : Word) : Vector (BitVec 32) 43 :=
  Vector.ofFn fun i =>
    if zero : i.val = 0 then statePointer.toBitVec
    else if statePart : i.val < 25 then (stateWord state extended ⟨i.val - 1, by omega⟩).toBitVec
    else if middle : i.val = 25 then messagePointer.toBitVec
    else if messagePart : i.val < 42 then (message[i.val - 26]'(by omega)).toBitVec
    else controller.toBitVec

def reads (input : Row.Input) : Vector (BitVec 32) 43 :=
  values input.statePointer input.messagePointer input.state input.extended input.message input.controller

def results (input : Row.Input) (output : Row.Output) : Vector (BitVec 32) 43 :=
  values input.statePointer input.messagePointer output.state output.extended input.message output.controller

def writes (input : Row.Input) (output : Row.Output) : List (Cell × BitVec 32) :=
  ((cells input).zip (results input output)).toList

/-- Extended-round state relation using independent preparation, scheduling,
    Clean eight-G, chaining and controller references, with all 43 atomic writes
    and their frame. The ABI's unequal bases alone do not exclude partial overlap
    (for example message = state + 64); this relation can then be nonfunctional.
    Accepted initialized memory history excludes conflicting same-clock writes.
    Reference correspondence is claimed under that history, not for every ABI input. -/
def Executes (before after : State) : Prop :=
  ∃ (input : Row.Input) (output : Row.Output), ABI input ∧ InputBounded input ∧ OutputBounded output ∧
    (∀ i : Fin 43, (cells input)[i].read before = .ok (reads input)[i] before) ∧
    Row.spec input output ∧ AtomicWrites (writes input output) before after

def Retires (before after : State) : Prop :=
  ∃ middle, Executes before middle ∧
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) middle = .ok () after

end Airbender.Blake2Round.Call
