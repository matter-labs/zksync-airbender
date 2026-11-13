module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.SubwordMemory.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.SubwordMemory

import_compiler_capture imported from "artifacts/compiler/subword-memory-cached.json" family "subword-memory"

end Airbender.Compiler.Captures.SubwordMemory

namespace Airbender.Compiler

/-- The subword-memory cached capture has the existing constraint description. Only its compiled layers differ. -/
def SubwordMemoryCachedDescriptionClaim : Prop :=
  { Captures.SubwordMemory.imported.circuit with layers := SubwordMemory.importedCircuit.layers } =
    SubwordMemory.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def SubwordMemoryCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.SubwordMemory.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.SubwordMemory.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def SubwordMemoryCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.SubwordMemory.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical

end Airbender.Compiler
