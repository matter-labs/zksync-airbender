import Airbender.Review.Keccak.Mix

namespace Airbender.Keccak

/-- Each native Rho call rotates one column in place. Clean's `rhoPi` names
    those writes after the Pi permutation; this table gives their destination
    indices in that original reference. The later controller proof must connect
    this logical renaming to the physical state indices across rounds. -/
def rhoDestinations : Vector (Vector (Fin 25) 5) 5 :=
  #v[#v[0, 8, 11, 19, 22], #v[2, 5, 13, 16, 24], #v[4, 7, 10, 18, 21],
    #v[1, 9, 12, 15, 23], #v[3, 6, 14, 17, 20]]

/-- Standard Rho rotation offsets, in Clean's column-major source order.
    Existing Rho proofs check them against the original `rhoPi` clauses. -/
def rhoRotations : Vector (Vector (Fin 64) 5) 5 :=
  #v[#v[0, 36, 3, 41, 18], #v[1, 44, 10, 45, 2], #v[62, 6, 43, 15, 61],
    #v[28, 55, 25, 21, 56], #v[27, 20, 39, 8, 14]]

/-- A native Theta column supplies the subsequent Rho column's actual limbs.
    The two x10 inputs identify the operations and column. `stateReads` and
    `dRead` interpret Theta's memory reads; `transport` connects actual writes
    to Rho reads. Neither bounds nor expected writes are assumed. Global memory
    matching and the schedule of all columns remain separate obligations. -/
structure ThetaRhoMapping {p : Nat} (state : Vector Nat 25) (d : Vector Nat 5)
    (column : Fin 5) (round : Fin 24) (theta rho : Nat → ZMod p) : Prop where
  thetaActive : theta Variables.execute = 1
  rhoActive : rho Variables.execute = 1
  thetaControl : (theta Variables.controlReadLo).val =
    (ControlState.mk 3 column ⟨round.val, by omega⟩).packed
  rhoControl : (rho Variables.controlReadLo).val =
    (ControlState.mk 4 column ⟨round.val, by omega⟩).packed
  stateReads : ∀ i : Fin 5, readLane theta ⟨i.val, by omega⟩ =
    state[5 * column.val + i.val]
  dRead : readLane theta 5 = d[column]
  transport : ∀ i : Fin 5, readLaneLimbs rho ⟨i.val, by omega⟩ =
    writeLaneLimbs theta ⟨i.val, by omega⟩

/-- Every rotated native write matches the original `rhoPi` after Theta,
    in the reference's destination order. The sixth scratch lane is preserved. -/
def RhoResult {p : Nat} (state : Vector Nat 25) (d : Vector Nat 5)
    (column : Fin 5) (rho : Nat → ZMod p) : Prop :=
  (∀ i : Fin 5, writeLane rho ⟨i.val, by omega⟩ =
    (Specs.Keccak256.rhoPi (Specs.Keccak256.thetaXor state d))[rhoDestinations[column][i]]) ∧
  writeLaneLimbs rho 5 = readLaneLimbs rho 5

end Airbender.Keccak
