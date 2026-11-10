import Airbender.Review.Circuits.Keccak.ControlUpdate

namespace Airbender.Keccak

/-- Control expected by the modeled special5 protocol: 24 rounds of 27 micro-operations,
    followed by the final Iota. The initialized-history proof derives these
    values for the actual imported rows; they are not inputs to that proof. -/
def scheduleControl (i : Fin 650) : ControlState :=
  let stage := i.val % 27
  ⟨⟨if stage < 5 then 0 else if stage < 7 then stage - 4 else if stage < 12 then 3
      else if stage < 17 then 4 else if (stage - 17) % 2 = 0 then 5 else 6,
      by split_ifs <;> omega⟩,
    ⟨if stage < 5 then stage else if stage < 7 then 0 else if stage < 12 then stage - 7
      else if stage < 17 then stage - 12 else (stage - 17) / 2,
      by have bound : stage < 27 := Nat.mod_lt _ (by decide); split_ifs <;> omega⟩,
    ⟨i.val / 27, by have := i.isLt; omega⟩⟩

end Airbender.Keccak
