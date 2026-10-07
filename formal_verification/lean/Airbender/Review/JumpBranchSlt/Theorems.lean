import Airbender.Proofs.JumpBranchSlt.Soundness
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt
namespace Comparison

/-- Shared soundness for SLT, SLTI, SLTU and SLTIU against native Sail register
    and PC effects. Alignment and the final-PC high bound are explicit
    interfaces; the imported arithmetic allows 32-bit PC wraparound. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.comparison_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Comparison

namespace Branch

/-- All six standard branches satisfy the shared native Sail state-transition
    property. Taken targets, fall-through and alignment follow from the artifact;
    decoding, input bounds, native reads and the final-PC high bound remain interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.branch_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Branch

namespace Jump

/-- Native JAL/JALR register and PC soundness, including x0 writes and wrapping
    links. JALR uses the explicit Machine-mode/MLPE-clear configuration interface. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.jump_soundness hp

theorem babyBear_soundness :
    circuitModel.SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide)

end Jump

end Airbender.JumpBranchSlt
