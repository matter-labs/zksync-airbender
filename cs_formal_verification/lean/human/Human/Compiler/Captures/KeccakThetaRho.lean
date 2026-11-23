module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.KeccakSplit.ThetaRho.Artifact

@[expose] public section
namespace Airbender.Compiler.Captures.KeccakThetaRho

import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_theta_rho_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "keccak-theta-rho", format_version := 1 }

end Airbender.Compiler.Captures.KeccakThetaRho

namespace Airbender.Compiler

/-- The cached split worker has the same constraint description as its no-cache capture. -/
def KeccakThetaRhoCachedDescriptionClaim : Prop :=
  { Captures.KeccakThetaRho.imported.circuit with layers := Airbender.Keccak.Split.ThetaRho.importedCircuit.layers } =
    Airbender.Keccak.Split.ThetaRho.importedCircuit

/-- Native base-field equations and source placement imply every description equation. -/
def KeccakThetaRhoCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.KeccakThetaRho.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.KeccakThetaRho.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.KeccakThetaRho.imported.circuit)

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native arithmetic and source placement have a concrete assignment. -/
def KeccakThetaRhoCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.KeccakThetaRho.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.KeccakThetaRho.imported.circuit physical logical

end Airbender.Compiler
