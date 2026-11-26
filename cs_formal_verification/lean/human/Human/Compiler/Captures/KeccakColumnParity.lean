module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact

@[expose] public section
namespace Airbender.Compiler.Captures.KeccakColumnParity

import_circuit importedCircuit from "../../circuit_defs/keccak_column_parity/generated/layout.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "keccak-column-parity", format_version := 1 }

end Airbender.Compiler.Captures.KeccakColumnParity

namespace Airbender.Compiler

/-- The cached split worker has the same constraint description as its no-cache capture. -/
def KeccakColumnParityCachedDescriptionClaim : Prop :=
  { Captures.KeccakColumnParity.imported.circuit with layers := Airbender.Keccak.Split.ColumnParity.importedCircuit.layers } =
    Airbender.Keccak.Split.ColumnParity.importedCircuit

/-- Native base-field equations and source placement imply every description equation. -/
def KeccakColumnParityCachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.KeccakColumnParity.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.KeccakColumnParity.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.KeccakColumnParity.imported.circuit)

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native arithmetic and source placement have a concrete assignment. -/
def KeccakColumnParityCachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.KeccakColumnParity.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.KeccakColumnParity.imported.circuit physical logical

end Airbender.Compiler
