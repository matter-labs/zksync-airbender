module
public import Human.Circuits.Blake2Round.Row
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Memory.Values
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace Airbender.Blake2Round.Mask
open Arithmetic
open scoped BigOperators

/-- Observable inputs of a native extended round with any Boolean round mask. -/
structure Input where
  /-- The x12 control word read by the worker. -/
  controller : Word
  /-- The ten independently checked native round bits. -/
  rounds : Fin 10 → Bool
  /-- The reduced-round control bit. -/
  reducedRounds : Bool
  /-- The compression control bit. -/
  compression : Bool
  /-- The right-node control bit. -/
  inputIsRight : Bool
  /-- The state-block pointer read from x10. -/
  statePointer : Word
  /-- The message-block pointer read from x11. -/
  messagePointer : Word
  /-- The eight chaining-state words read from RAM. -/
  state : Vector Word 8
  /-- The sixteen working-state words read from RAM. -/
  extended : Vector Word 16
  /-- The sixteen message words read from RAM. -/
  message : Vector Word 16

/-- Observable writes and addresses of the same worker row. -/
structure Output where
  /-- The x12 control word written by the worker. -/
  controller : Word
  /-- The eight chaining-state words written to RAM. -/
  state : Vector Word 8
  /-- The sixteen working-state words written to RAM. -/
  extended : Vector Word 16
  /-- The imported indirect RAM addresses. -/
  addresses : Addresses.Output

/-- Each selected SIGMA row contributes to both native message limbs. -/
def scheduledMessage (rounds : Fin 10 → Bool) (message : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun position =>
    let word := fun round : Fin 10 =>
      message[Fin.ofNat 16 Blake2G.Control.messageSchedule[round][position]]
    ⟨∑ round : Fin 10, if rounds round then (word round).lo else 0,
     ∑ round : Fin 10, if rounds round then (word round).hi else 0⟩

/-- Bit zero selects preparation independently of all other round bits. -/
def preparationInput (input : Input) : Preparation.Input :=
  ⟨input.rounds 0, input.compression, input.inputIsRight, input.state, input.extended, input.message⟩

/-- Bit six has priority over bit nine in the native final-round flag. -/
def isFinal (input : Input) : Bool := if input.rounds 6 then input.reducedRounds else input.rounds 9

/-- Native Boolean-mask behavior. Word sums use the existing modular G reference.
    No exclusive-mask condition is imposed. -/
def spec (input : Input) (output : Output) : Prop :=
  let prepared := Preparation.step (preparationInput input)
  Control.spec input.controller output.controller ∧
  Mixing.spec ⟨prepared.extended, scheduledMessage input.rounds prepared.message⟩ output.extended ∧
  (if isFinal input then
    output.state.map Word.value = Vector.ofFn fun i : Fin 8 =>
      prepared.chaining[i].value ^^^ output.extended[i.val].value ^^^ output.extended[8 + i.val].value
   else output.state = input.state) ∧
  Addresses.spec ⟨input.statePointer, input.messagePointer⟩ output.addresses

/-- Initialized memory supplies bounded source words. The native equations supply all internal values. -/
structure Assumptions (input : Input) : Prop where
  /-- The input control word has two canonical limbs. -/
  controller : input.controller.Bounded
  /-- Both input pointers have two canonical limbs. -/
  pointers : input.statePointer.Bounded ∧ input.messagePointer.Bounded
  /-- Every input chaining-state word has two canonical limbs. -/
  state : ∀ i : Fin 8, input.state[i].Bounded
  /-- Every input working-state word has two canonical limbs. -/
  extended : ∀ i : Fin 16, input.extended[i].Bounded
  /-- Every input message word has two canonical limbs. -/
  message : ∀ i : Fin 16, input.message[i].Bounded

/-- Read the two raw value limbs of one imported native memory port. -/
def readWord (w : Nat → ZMod babyBearModulus) (index : Fin 43) : Word :=
  (Trace.readToken w (importedConstraintsMemoryPorts[index.val]'index.isLt)).word

/-- Read the two raw write-value limbs of one imported native memory port. -/
def writtenWord (w : Nat → ZMod babyBearModulus) (index : Fin 43) : Word :=
  let code := (importedConstraintsMemoryPorts[index.val]'index.isLt).writeCode w
  ⟨(Nat.unpair code).1, (Nat.unpair code).2⟩

/-- Bind observable words and Boolean controls to the imported row. -/
structure Mapping (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus) : Prop where
  /-- The input control limbs are the worker's actual x12 read. -/
  controller : input.controller = readWord w 42
  /-- The output control limbs are the worker's actual x12 write. -/
  controllerOutput : output.controller = writtenWord w 42
  /-- The state pointer is the worker's actual x10 read. -/
  statePointer : input.statePointer = readWord w 0
  /-- The message pointer is the worker's actual x11 read. -/
  messagePointer : input.messagePointer = readWord w 25
  /-- Each mask bit binds the corresponding native Boolean column. -/
  rounds : ∀ round : Fin 10, w (142 + round.val) = if input.rounds round then 1 else 0
  /-- The reduced-round flag binds its native Boolean column. -/
  reduced : w 139 = if input.reducedRounds then 1 else 0
  /-- The compression flag binds its native Boolean column. -/
  compression : w 141 = if input.compression then 1 else 0
  /-- The right-node flag binds its native Boolean column. -/
  inputIsRight : w 140 = if input.inputIsRight then 1 else 0
  /-- The chaining inputs are the actual RAM read columns. -/
  state : input.state = Vector.ofFn fun i => readWord w ⟨1 + i.val, by have := i.isLt; omega⟩
  /-- The working inputs are the actual RAM read columns. -/
  extended : input.extended = Vector.ofFn fun i => readWord w ⟨9 + i.val, by have := i.isLt; omega⟩
  /-- The message inputs are the actual RAM read columns. -/
  message : input.message = Vector.ofFn fun i => readWord w ⟨26 + i.val, by have := i.isLt; omega⟩
  /-- The chaining outputs are the actual RAM write columns. -/
  stateOutput : output.state = Vector.ofFn fun i => writtenWord w ⟨1 + i.val, by have := i.isLt; omega⟩
  /-- The working outputs are the actual RAM write columns. -/
  extendedOutput : output.extended = Vector.ofFn fun i => writtenWord w ⟨9 + i.val, by have := i.isLt; omega⟩
  /-- The output addresses are the imported native indirect addresses. -/
  addresses : output.addresses = importedConstraintsIndirectPorts.map (fun port => port.address w)

/-- Every accepted extended-round row follows the native Boolean-mask reference.
    Source bounds come from initialized memory. Mapping supplies no internal schedule, G output or finalization result. -/
def SoundnessClaim : Prop :=
  ∀ (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus),
    Assumptions input →
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable) →
    Mapping input output w → spec input output

/-- The native row premises admit an assignment. -/
def SatisfiableClaim : Prop :=
  ∃ (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus),
    Assumptions input ∧
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable) ∧
    Mapping input output w

end Airbender.Blake2Round.Mask
