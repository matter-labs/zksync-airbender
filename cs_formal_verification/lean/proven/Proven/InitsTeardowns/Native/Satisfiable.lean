module
public import Human.Circuits.InitsTeardowns.Native.Model

@[expose] public section

namespace Airbender.InitsTeardowns.Native.Proofs

/-- Zero product weights and unit wires satisfy every memory-product gate. -/
theorem accepted_unit (artifact : Artifact) :
    Accepted artifact (p := p) (E := ZMod p) ⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩
      (fun _ _ => 0) (fun _ _ => 1) := by
  intro row gate _
  cases gate <;> simp [Gate.Sat, Leaf.factor]

end Airbender.InitsTeardowns.Native.Proofs
