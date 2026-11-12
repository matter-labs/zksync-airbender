module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.Bigint.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.Bigint

import_compiler_capture imported from "artifacts/compiler/bigint-cached.json" family "bigint"

end Airbender.Compiler.Captures.Bigint

namespace Airbender.Compiler

/-- The bigint cached capture has the existing constraint description. Only its compiled layers differ. -/
def BigintCachedDescriptionClaim : Prop :=
  { Captures.Bigint.imported.circuit with layers := Bigint.importedCircuit.layers } =
    Bigint.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def BigintCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.Bigint.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.Bigint.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.Bigint.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def BigintCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.Bigint.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.Bigint.imported.circuit physical logical

end Airbender.Compiler
