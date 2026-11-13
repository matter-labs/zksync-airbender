module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.Blake2Round.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.BlakeRound

import_compiler_capture imported from "artifacts/compiler/blake-round-cached.json" family "blake-round"

end Airbender.Compiler.Captures.BlakeRound

namespace Airbender.Compiler

/-- The blake-round cached capture has the existing constraint description. Only its compiled layers differ. -/
def BlakeRoundCachedDescriptionClaim : Prop :=
  { Captures.BlakeRound.imported.circuit with layers := Blake2Round.importedCircuit.layers } =
    Blake2Round.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def BlakeRoundCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.BlakeRound.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.BlakeRound.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.BlakeRound.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def BlakeRoundCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.BlakeRound.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.BlakeRound.imported.circuit physical logical

end Airbender.Compiler
