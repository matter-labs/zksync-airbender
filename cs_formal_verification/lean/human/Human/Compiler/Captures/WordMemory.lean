module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.WordMemory.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.WordMemory

import_compiler_capture imported from "artifacts/compiler/word-memory-cached.json" family "word-memory"

end Airbender.Compiler.Captures.WordMemory

namespace Airbender.Compiler

/-- The word-memory cached capture has the existing constraint description. Only its compiled layers differ. -/
def WordMemoryCachedDescriptionClaim : Prop :=
  { Captures.WordMemory.imported.circuit with layers := WordMemory.importedCircuit.layers } =
    WordMemory.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def WordMemoryCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.WordMemory.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.WordMemory.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.WordMemory.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def WordMemoryCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.WordMemory.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.WordMemory.imported.circuit physical logical

end Airbender.Compiler
