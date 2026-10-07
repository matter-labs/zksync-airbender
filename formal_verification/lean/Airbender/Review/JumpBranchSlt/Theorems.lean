import Airbender.Proofs.JumpBranchSlt.Soundness
import Airbender.Proofs.JumpBranchSlt.BranchSoundness
import Airbender.Proofs.JumpBranchSlt.JumpSoundness
import Airbender.Proofs.JumpBranchSlt.PCState
import Airbender.Proofs.BabyBear

namespace Airbender.JumpBranchSlt

/-- Supply the final-PC range premise for this family's local soundness claims.
    The low bound follows from imported lookups; the high bound follows from
    logical state matching and decoder membership, including the terminal boundary. -/
theorem final_pc_bounds {p n : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {context : PCState.Context p n} {w : Nat → ZMod p}
    (global : PCState.Interface context)
    (outgoing : PCState.Outgoing context (w Variables.finalPCLo, w Variables.finalPCHi))
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w Variables.finalPCLo).val < Arithmetic.limbBase ∧
      (w Variables.finalPCHi).val < Arithmetic.limbBase :=
  Proofs.final_pc_bounds hp global outgoing h

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
