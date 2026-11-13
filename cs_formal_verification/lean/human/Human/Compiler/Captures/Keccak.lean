module
public import Human.Import.CompilerCapture
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.Keccak.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.Keccak

import_compiler_capture imported from "artifacts/compiler/keccak-cached.json" family "keccak"

end Airbender.Compiler.Captures.Keccak

namespace Airbender.Compiler

/-- The keccak cached capture has the existing constraint description. Only its compiled layers differ. -/
def KeccakCachedDescriptionClaim : Prop :=
  { Captures.Keccak.imported.circuit with layers := Keccak.importedCircuit.layers } =
    Keccak.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def KeccakCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.Keccak.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.Keccak.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.Keccak.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def KeccakCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.Keccak.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.Keccak.imported.circuit physical logical

end Airbender.Compiler
