module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.JumpBranchSlt.Artifact

@[expose] public section

namespace Airbender.Compiler.Captures.JumpBranch

import_circuit importedCircuit from "../../cs/compiled_circuits/jump_branch_slt_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "jump-branch", format_version := 1 }

end Airbender.Compiler.Captures.JumpBranch

namespace Airbender.Compiler

/-- The jump-branch cached capture has the existing constraint description. Only its compiled layers differ. -/
def JumpBranchCachedDescriptionClaim : Prop :=
  { Captures.JumpBranch.imported.circuit with layers := JumpBranchSlt.importedCircuit.layers } =
    JumpBranchSlt.importedCircuit

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native sparse base-field gate equations imply the shared description's arithmetic equations.
    The placement interface binds logical witness columns to physical addresses. Lookup and memory arguments are separate. -/
def JumpBranchCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.JumpBranch.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.JumpBranch.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.JumpBranch.imported.circuit)

/-- The native arithmetic and placement premises have a physical and logical assignment. -/
def JumpBranchCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.JumpBranch.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.JumpBranch.imported.circuit physical logical

end Airbender.Compiler
