module
public import Proven.UnifiedReduced.Proth120.Witness
public import Human.Circuits.UnifiedReduced.Proth120Execution

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.Witness
open Trace

/-- At PC zero the wrap fetches the four little-endian bytes of `mop.rr.3 x3, x1, x2`. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  mem _ := 0
  rom a := match a.toNat with
    | 0 => 0xf3 | 1 => 0xc1 | 2 => 0x20 | 3 => 0x8e | _ => 0

def cells : List Cell := [.register 1, .register 2, .register 3]

theorem fma_inputs : RowInputs cells 0 (assignment .fma) initial initial where
  constraints := holds .fma (ROM.wordsRV initial)
  active := rfl
  fetch := ⟨rfl, by decide⟩
  decoded := ⟨.mop .fma 3 1 2, ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 64, 0⟩,
    by kernel_rfl, by kernel_rfl, by kernel_rfl⟩
  bounded := ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩
  aligned := by
    intro c hc
    simp [cells] at hc
    rcases hc with rfl | rfl | rfl <;> trivial
  history := by
    apply RVHistory.cons (cell := .register 3) (middle := initial)
    · apply RVHistory.cons (cell := .register 2) (middle := initial)
      · exact RVHistory.cons (RVHistory.nil _) (.register 1) (by simp [cells]) rfl rfl rfl
      · simp [cells]
      all_goals rfl
    · simp [cells]
    all_goals rfl

end Airbender.UnifiedReduced.Proth120.Witness
