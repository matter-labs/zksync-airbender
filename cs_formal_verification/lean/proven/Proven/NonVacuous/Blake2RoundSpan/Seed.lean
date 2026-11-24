module
public import Proven.NonVacuous.Blake2RoundSpan.Block

@[expose] public section
namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Trace Blake2GSpan

/-- The starting state: the two pointers and the first round's control word, RAM a byte pattern. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 0x400000 else if i = 11 then 0x400080 else if i = 12 then 0x80000 else 0
  rom _ := 0
  mem address := BitVec.ofNat 8 (address.toNat * 37 + 11)

/-- The seed tokens read from `before`. -/
def seed : Memory := fun cell => cell.initialToken ((cell.readRV before).getD 0)

theorem seed_inv : Inv seed 1 0 where
  address _ _ := rfl
  high _ _ := rfl
  time _ _ := by simp [seed, Cell.initialToken]
  words c _ := seed_bounded c _
  state := by decide +kernel
  message := by decide +kernel
  control := by decide +kernel

end Airbender.NonVacuous.Blake2RoundSpan
