module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.MulDiv.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.MulDiv

import_circuit importedCircuit from "../../circuit_defs/unrolled_circuits/mul_div_unsigned/generated/layout.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "mul-div", format_version := 1 }

end Airbender.Compiler.Captures.MulDiv

namespace Airbender.Compiler

/-- The mul-div cached capture has the existing constraint description. Only its compiled layers differ. -/
def MulDivCachedDescriptionClaim : Prop :=
  { Captures.MulDiv.imported.circuit with layers := MulDiv.importedCircuit.layers } =
    MulDiv.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def MulDivCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.MulDiv.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.MulDiv.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.MulDiv.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def MulDivCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.MulDiv.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.MulDiv.imported.circuit physical logical

end Airbender.Compiler
