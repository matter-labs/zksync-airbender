import Airbender.Review.Circuits.Keccak.Iota
import Airbender.Review.Circuits.Keccak.Tables.Controller
import Airbender.Review.Helpers.Memory.AtomicWrites
import Airbender.Review.Helpers.Memory.ROM

namespace Airbender.Keccak.Call
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

structure Arguments where
  control : ControlState
  pointer : Word
  lanes : Vector Nat 6

/-- The existing successful 649-call schedule uses rounds 0–23 and one final
    Iota at round 24. Unsupported native fallback controls are outside it. -/
def Supported (control : ControlState) : Prop :=
  control.round.val ≤ 24 ∧ (control.mode.val = 0 ∨ control.round.val < 24)

structure ABI (input : Arguments) : Prop where
  control : Supported input.control
  pointer : input.pointer.Bounded
  ram : ROM.limit ≤ input.pointer.toBitVec.toNat
  aligned : input.pointer.toBitVec.toNat % 256 = 0
  lanes : ∀ i : Fin 6, input.lanes[i] < 2 ^ 64

def key (control : ControlState) : Fin 4096 :=
  ⟨control.packed + 2048, by
    unfold ControlState.packed
    have := control.mode.isLt
    have := control.iteration.isLt
    have := control.round.isLt
    omega⟩

def indices (control : ControlState) : Vector Nat 6 := Controller.rows (key control)

/-- Pure column embedding for the original Iota/Theta-C references. Only the
    selected five lanes contribute; the scratch lane's old value is unused. -/
def columnState (lanes : Vector Nat 6) (column : Fin 5) : Vector Nat 25 :=
  Vector.ofFn fun i => if i.val / 5 = column.val then lanes[i.val % 5]'(by omega) else 0

def iotaColumn (lanes : Vector Nat 6) (column : Fin 5) (round : Fin 25) : Vector Nat 6 :=
  let changed := iotaState (columnState lanes column) round
  Vector.ofFn fun i => if first : i.val < 5 then changed[5 * column.val + i.val]'(by omega)
    else (Specs.Keccak256.thetaC changed)[column]

/-- Independent seven-mode micro-operation reference. Iota and its parity use
    the original Clean functions; the other modes retain the already reviewed
    column-mix, Theta, Rho and split-Chi clauses. -/
def Operation (control : ControlState) (input output : Vector Nat 6) : Prop :=
  match control.mode.val with
  | 0 => ∃ round : Fin 25, control.round.val = round.val ∧
      output = iotaColumn input control.iteration round
  | 1 => output = #v[input[0] ^^^ rotLeft64 input[2] 1, input[1],
      input[2] ^^^ rotLeft64 input[4] 1, input[3], input[4], rotLeft64 input[0] 1]
  | 2 => output = #v[input[0], input[1] ^^^ rotLeft64 input[3] 1,
      input[2], input[3] ^^^ input[5], input[4] ^^^ rotLeft64 input[1] 1, input[5]]
  | 3 => output = Vector.ofFn (fun i => if i.val < 5 then input[i] ^^^ input[5] else input[5])
  | 4 => output = Vector.ofFn (fun i => if first : i.val < 5 then
      rotLeft64 input[i] ((rhoRotations[control.iteration])[i.val]'first) else input[5])
  | 5 => output = #v[input[0] ^^^ ((not64 input[1]) &&& input[2]),
      input[1] ^^^ ((not64 input[2]) &&& input[3]), input[2], input[3],
      (not64 input[0]) &&& input[1], input[0]]
  | _ => output = #v[input[0] ^^^ input[3], input[1] ^^^ ((not64 input[2]) &&& input[0]),
      input[2] ^^^ ((not64 input[0]) &&& input[4]), input[3], input[4], input[5]]

def half (lane : Nat) (high : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (if high then lane / 2 ^ 32 else lane)

def cells (input : Arguments) : Vector Cell 14 :=
  Vector.ofFn fun i =>
    if zero : i.val = 0 then .register 10
    else if pointer : i.val = 1 then .register 11
    else .ram (input.pointer.toBitVec + BitVec.ofNat 32
      (8 * (indices input.control)[(i.val - 2) / 2]'(by omega) + 4 * ((i.val - 2) % 2)))

def values (controller pointer : BitVec 32) (lanes : Vector Nat 6) : Vector (BitVec 32) 14 :=
  Vector.ofFn fun i =>
    if zero : i.val = 0 then controller
    else if pointerCell : i.val = 1 then pointer
    else half (lanes[(i.val - 2) / 2]'(by omega)) (decide ((i.val - 2) % 2 = 1))

def reads (input : Arguments) : Vector (BitVec 32) 14 :=
  values (BitVec.ofNat 32 input.control.packed) input.pointer.toBitVec input.lanes

def results (input : Arguments) (output : Vector Nat 6) : Vector (BitVec 32) 14 :=
  values (BitVec.ofNat 32 input.control.nextPacked) input.pointer.toBitVec output

def writes (input : Arguments) (output : Vector Nat 6) : List (Cell × BitVec 32) :=
  ((cells input).zip (results input output)).toList

/-- Complete supported micro-call effect in Sail state. The independently
    selected addresses and seven-mode reference fix every actual write and the
    unchanged frame; no circuit assignment appears in this relation. -/
def Executes (before after : State) : Prop :=
  ∃ (input : Arguments) (output : Vector Nat 6), ABI input ∧ (∀ i : Fin 6, output[i] < 2 ^ 64) ∧
    (∀ i : Fin 14, (cells input)[i].read before = .ok (reads input)[i] before) ∧
    Operation input.control input.lanes output ∧ AtomicWrites (writes input output) before after

def Retires (before after : State) : Prop :=
  ∃ middle, Executes before middle ∧
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) middle = .ok () after

end Airbender.Keccak.Call
