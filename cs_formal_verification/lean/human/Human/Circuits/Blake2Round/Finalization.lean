module
public import Human.Circuits.Blake2Round.Mixing

@[expose] public section

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

end Airbender.Blake2Round.Finalization
