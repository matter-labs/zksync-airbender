module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.Blake2G.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.BlakeG

import_circuit importedCircuit from "../../cs/compiled_circuits/blake2_g_function_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "blake-g", format_version := 1 }

end Airbender.Compiler.Captures.BlakeG

namespace Airbender.Compiler

/-- The blake-g cached capture has the existing constraint description. Only its compiled layers differ. -/
def BlakeGCachedDescriptionClaim : Prop :=
  { Captures.BlakeG.imported.circuit with layers := Blake2G.importedCircuit.layers } =
    Blake2G.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def BlakeGCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.BlakeG.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.BlakeG.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.BlakeG.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def BlakeGCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.BlakeG.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.BlakeG.imported.circuit physical logical

end Airbender.Compiler
