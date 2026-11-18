module
public import Human.Circuits.Blake2Round.Preparation
public import Human.Circuits.Blake2Round.Tables.Setup

@[expose] public section

namespace Airbender.Blake2Round.Mixing

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Input where
  state : Vector Arithmetic.Word 16
  message : Vector Arithmetic.Word 16

abbrev Output := Vector Arithmetic.Word 16

/-- The eight mixing calls use Clean's existing round function. Message words
    are already SIGMA-selected; preparation and scheduling have separate claims. -/
def spec (input : Input) (output : Output) : Prop :=
  output.map Arithmetic.Word.value =
    Specs.BLAKE3.round (input.state.map Arithmetic.Word.value)
      (input.message.map Arithmetic.Word.value)

end Airbender.Blake2Round.Mixing
