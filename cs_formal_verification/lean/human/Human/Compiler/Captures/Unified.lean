module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.UnifiedReduced.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.Unified

import_compiler_capture imported from "artifacts/compiler/unified-cached.json" family "unified"

end Airbender.Compiler.Captures.Unified

namespace Airbender.Compiler

/-- The unified cached capture has the existing constraint description. Only its compiled layers differ. -/
def UnifiedCachedDescriptionClaim : Prop :=
  { Captures.Unified.imported.circuit with layers := UnifiedReduced.importedCircuit.layers } =
    UnifiedReduced.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def UnifiedCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.Unified.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.Unified.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.Unified.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def UnifiedCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.Unified.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.Unified.imported.circuit physical logical

end Airbender.Compiler
