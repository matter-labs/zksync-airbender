import Airbender.Proofs.Blake2G.Frame
import Airbender.Proofs.Blake2G.Soundness

namespace Airbender.Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Canonical input words of the stable arithmetic frame. -/
def Frame.input {p : Nat} (frame : Frame p) : Input :=
  ⟨⟨⟨frame.inputs[0].val, frame.inputs[1].val⟩,
      ⟨frame.inputs[2].val, frame.inputs[3].val⟩,
      ⟨frame.inputs[4].val, frame.inputs[5].val⟩,
      ⟨frame.inputs[6].val, frame.inputs[7].val⟩⟩,
    ⟨frame.inputs[8].val, frame.inputs[9].val⟩,
    ⟨frame.inputs[10].val, frame.inputs[11].val⟩⟩

def Frame.output {p : Nat} (frame : Frame p) : Words :=
  ⟨⟨(frame.assignment 17).val, (frame.assignment 18).val⟩,
    ⟨(frame.assignment 21).val, (frame.assignment 22).val⟩,
    ⟨(frame.assignment 25).val, (frame.assignment 26).val⟩,
    ⟨(frame.assignment 29).val, (frame.assignment 30).val⟩⟩

/-- The stable frame supplies the old G mapping once for every embedding. -/
theorem Frame.mapping {p : Nat} (frame : Frame p) :
    WordMapping frame.input frame.output frame.assignment := by
  constructor <;> rfl

/-- Reuse the existing arithmetic and pinned reference proof unchanged. -/
theorem Frame.Certificate.soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {frame : Frame p}
    (control : Fin 512 → Vector Nat 7)
    (certificate : frame.Certificate (setupTable control))
    (interface : InterfaceAssumptions frame.input frame.output frame.assignment) :
    spec frame.input frame.output :=
  mixing_soundness hp compatible control frame.input frame.output frame.assignment
    ⟨interface, certificate.holds, frame.mapping⟩

end Airbender.Blake2G.Proofs
