module
public import Human.Circuits.Blake2Round.Preparation
public import Human.Circuits.Blake2G.Tables.Controller

@[expose] public section

namespace Airbender.Blake2Round.Schedule
open Arithmetic

structure Input where
  round : Fin 10
  message : Vector Word 16

abbrev Output := Vector Word 16

/-- Reuse the same BLAKE2s SIGMA schedule as the G controller. -/
def step (input : Input) : Output :=
  Blake2G.Control.messageSchedule[input.round].map fun column =>
    input.message[Fin.ofNat 16 column]

end Airbender.Blake2Round.Schedule
