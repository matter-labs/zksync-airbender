import Human.Circuits.Blake2Round.Mixing
import Slop.Blake2Round.DiagonalG
import Slop.Blake2Round.Reference
import Slop.Blake2Round.ArtifactChecks

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def gOutput {p : Nat} (w : Nat → ZMod p) : Blake2G.Words :=
  ⟨⟨(w 17).val, (w 18).val⟩, ⟨(w 21).val, (w 22).val⟩,
    ⟨(w 25).val, (w 26).val⟩, ⟨(w 29).val, (w 30).val⟩⟩

def columnOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  gOutput (columnGAssignment call w)

def diagonalOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  gOutput (diagonalGAssignment call w)

end Airbender.Blake2Round.Proofs
