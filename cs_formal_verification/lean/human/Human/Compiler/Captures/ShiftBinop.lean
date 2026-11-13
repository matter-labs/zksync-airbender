module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.ShiftBinop.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.ShiftBinop

import_compiler_capture imported from "artifacts/compiler/shift-binop-cached.json" family "shift-binop"

end Airbender.Compiler.Captures.ShiftBinop

namespace Airbender.Compiler

/-- The shift-binop cached capture has the existing constraint description. Only its compiled layers differ. -/
def ShiftBinopCachedDescriptionClaim : Prop :=
  { Captures.ShiftBinop.imported.circuit with layers := ShiftBinop.importedCircuit.layers } =
    ShiftBinop.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def ShiftBinopCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.ShiftBinop.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.ShiftBinop.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def ShiftBinopCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.ShiftBinop.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.ShiftBinop.imported.circuit physical logical

end Airbender.Compiler
