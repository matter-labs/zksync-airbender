import Airbender.Review.Circuits.Blake2G.Model
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true

def gOutput {p : Nat} (w : Nat → ZMod p) : Blake2G.Words :=
  ⟨⟨(w 17).val, (w 18).val⟩, ⟨(w 21).val, (w 22).val⟩,
    ⟨(w 25).val, (w 26).val⟩, ⟨(w 29).val, (w 30).val⟩⟩

def columnOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  gOutput (nativeColumnAssignment call w)

def diagonalOutputs {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  gOutput (nativeDiagonalAssignment call w)

end Airbender.Blake2Round.Proofs
