import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.Mersenne31

namespace Airbender.AddSub
open Reference.RiscV

/-- Accepted v2 ADD/ADDI/SUB/LUI/AUIPC rows have original Sail destination and
    PC effects under the explicit local interfaces in Model, including x0 and
    aligned 32-bit PC wraparound. Initialized whole traces remain pending. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 196608 < p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  Proofs.soundness hp

/-- Native v2 field instance; coefficient decoding is canonical Mersenne31. -/
theorem mersenne31_soundness :
    (circuitModel (p := mersenne31Modulus)).SoundnessUnder InterfaceAssumptions Sail.spec :=
  soundness (by decide)

end Airbender.AddSub
