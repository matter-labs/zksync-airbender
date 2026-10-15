import Airbender.Review.Circuits.Blake2G.Addresses
import Airbender.Review.Helpers.Memory.AtomicWrites
import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Blake2G.Call
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Successful micro-call arguments within the pinned complete G protocol.
    The controller and pointers select the physical words independently of
    native ports; the operand words are read from that Sail pre-state. -/
structure Arguments where
  addresses : Addresses.Input
  operands : Input

structure ABI (addresses : Addresses.Input) : Prop where
  active : addresses.controller.active = true
  /-- Successful public spans use a G index in their selected round schedule. -/
  counter : addresses.controller.register.val % 128 <
    if addresses.controller.register.val / 128 = 0 then 80 else 56
  bounded : addresses.statePointer.Bounded ∧ addresses.messagePointer.Bounded
  ram : ROM.limit ≤ addresses.statePointer.toBitVec.toNat ∧
    ROM.limit ≤ addresses.messagePointer.toBitVec.toNat
  aligned : addresses.statePointer.toBitVec.toNat % 64 = 0 ∧
    addresses.messagePointer.toBitVec.toNat % 64 = 0
  distinct : addresses.statePointer.toBitVec ≠ addresses.messagePointer.toBitVec

def BoundedWords (words : Words) : Prop :=
  words.a.Bounded ∧ words.b.Bounded ∧ words.c.Bounded ∧ words.d.Bounded

def cells (addresses : Addresses.Input) : Vector Cell 9 :=
  let selected := Addresses.expected addresses
  #v[.register 10, .ram selected[0], .ram selected[1], .ram selected[2], .ram selected[3],
    .register 11, .ram selected[4], .ram selected[5], .register 12]

def reads (arguments : Arguments) : Vector (BitVec 32) 9 :=
  let input := arguments.operands
  #v[arguments.addresses.statePointer.toBitVec,
    input.state.a.toBitVec, input.state.b.toBitVec, input.state.c.toBitVec, input.state.d.toBitVec,
    arguments.addresses.messagePointer.toBitVec, input.mx.toBitVec, input.my.toBitVec,
    (Word.mk arguments.addresses.controller.register.val 0).toBitVec]

def results (arguments : Arguments) (output : Words) : Vector (BitVec 32) 9 :=
  #v[arguments.addresses.statePointer.toBitVec,
    output.a.toBitVec, output.b.toBitVec, output.c.toBitVec, output.d.toBitVec,
    arguments.addresses.messagePointer.toBitVec, arguments.operands.mx.toBitVec,
    arguments.operands.my.toBitVec, (Control.step arguments.addresses.controller).register.toBitVec]

def writes (arguments : Arguments) (output : Words) : List (Cell × BitVec 32) :=
  ((cells arguments.addresses).zip (results arguments output)).toList

/-- Complete successful G micro-operation, including the unchanged frame.
    The pure controller selects addresses and its next x12 value; the existing
    Clean G reference fixes the four changed words. Complete-span scheduling
    is a separate existing public protocol condition, not an input result. -/
def Executes (before after : State) : Prop :=
  ∃ (arguments : Arguments) (output : Words),
    ABI arguments.addresses ∧ BoundedWords arguments.operands.state ∧
    arguments.operands.mx.Bounded ∧ arguments.operands.my.Bounded ∧ BoundedWords output ∧
    (∀ i : Fin 9, (cells arguments.addresses)[i].read before = .ok (reads arguments)[i] before) ∧
    spec arguments.operands output ∧ AtomicWrites (writes arguments output) before after

def Retires (before after : State) : Prop :=
  ∃ middle, Executes before middle ∧
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) middle =
      .ok () after

end Airbender.Blake2G.Call
