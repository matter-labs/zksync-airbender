import Human.Circuits.Blake2Round.Mixing

namespace Airbender.Blake2Round.Finalization

set_option maxRecDepth 16384

structure Input where
  round : Fin 10
  reducedRounds : Bool
  state : Vector Arithmetic.Word 8
  chaining : Vector Arithmetic.Word 8
  extended : Vector Arithmetic.Word 16

abbrev Output := Vector Arithmetic.Word 8

/-- Airbender finishes at round ten, or at round seven in reduced-round mode. -/
def isFinal (input : Input) : Bool :=
  input.round == 9 || (input.round == 6 && input.reducedRounds)

/-- Finalization writes the three-way XOR on final rounds and preserves the
    original chaining-state reads otherwise. Extended-state writes are separate. -/
def spec (input : Input) (output : Output) : Prop :=
  if isFinal input then
    output.map Arithmetic.Word.value = Vector.ofFn fun i : Fin 8 =>
      input.chaining[i].value ^^^ input.extended[i.val].value ^^^ input.extended[8 + i.val].value
  else output = input.state

def stateWrites : Vector (Nat × Nat) 8 := Vector.ofFn fun i => (7 + 4 * i.val, 8 + 4 * i.val)

structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  reduced : w Variables.controlBits[0] = if input.reducedRounds then 1 else 0
  state : input.state = Preparation.words w Variables.stateReads
  chaining : input.chaining = Preparation.words w Variables.chainingInputs
  extended : input.extended = Preparation.words w Mixing.extendedWrites
  output : output = Preparation.words w stateWrites

/-- Only the caller's exclusive round mask is external. Final XOR input and
    output bounds follow from the imported queries. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Output) (w : Nat → ZMod p) : Prop where
  roundMask : Control.RoundMask w input.round

/-- Non-final preservation also holds without serialized-inverse compatibility. -/
structure NonFinalAssumptions {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop
    extends InterfaceAssumptions input output w where
  nonFinal : input.round.val ≠ 9 ∧ (input.reducedRounds = true → input.round.val ≠ 6)

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat
    (Verification.environment w) (importedConstraints setupTable)
  represents := WordMapping

end Airbender.Blake2Round.Finalization
