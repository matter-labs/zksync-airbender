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

/-- A final round writes the three-way XOR. Other rounds preserve the chaining-state reads. -/
def result (final : Bool) (state chaining : Vector Arithmetic.Word 8)
    (extended : Vector Arithmetic.Word 16) (output : Output) : Prop :=
  if final then
    output.map Arithmetic.Word.value = Vector.ofFn fun i : Fin 8 =>
      chaining[i].value ^^^ extended[i.val].value ^^^ extended[8 + i.val].value
  else output = state

/-- Finalization uses the shared XOR and preservation rule with the selected final-round flag. -/
def spec (input : Input) (output : Output) : Prop :=
  result (isFinal input) input.state input.chaining input.extended output

end Airbender.Blake2Round.Finalization
