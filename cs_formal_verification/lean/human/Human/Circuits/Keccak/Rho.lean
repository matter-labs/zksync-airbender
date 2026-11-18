module
public import Human.Circuits.Keccak.Theta
public import Human.Circuits.Keccak.ControlUpdate

@[expose] public section

namespace Airbender.Keccak

/-- Standard Rho rotation offsets, in Clean's column-major source order.
    Existing Rho proofs check them against the original `rhoPi` clauses. -/
def rhoRotations : Vector (Vector (Fin 64) 5) 5 :=
  #v[#v[0, 36, 3, 41, 18], #v[1, 44, 10, 45, 2], #v[62, 6, 43, 15, 61],
    #v[28, 55, 25, 21, 56], #v[27, 20, 39, 8, 14]]

end Airbender.Keccak
