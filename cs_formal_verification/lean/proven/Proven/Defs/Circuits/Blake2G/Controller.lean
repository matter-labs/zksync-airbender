module
public import Human.Circuits.Blake2G.Model
public import Human.Circuits.Blake2G.Controller

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2G/Controller.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2G.Control
def Input.key (input : Input) : Fin 512 :=
  ⟨input.register.val + if input.active then 256 else 0, by
    have bound := input.register.isLt
    cases input.active <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
def spec (input : Input) (output : Output) : Prop := output = step input
end Airbender.Blake2G.Control
