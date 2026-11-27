module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.AddSub.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.AddSub

import_circuit importedCircuit from "../../circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "add-sub", format_version := 1 }

end Airbender.Compiler.Captures.AddSub

namespace Airbender.Compiler

/-- The add-sub cached capture has the existing constraint description. Only its compiled layers differ. -/
def AddSubCachedDescriptionClaim : Prop :=
  { Captures.AddSub.imported.circuit with layers := AddSub.importedCircuit.layers } =
    AddSub.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def AddSubCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.AddSub.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.AddSub.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.AddSub.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def AddSubCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.AddSub.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.AddSub.imported.circuit physical logical

end Airbender.Compiler
