module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Helpers.Properties
public import Human.Circuits.KeccakSplit.Chi5.Artifact

@[expose] public section
namespace Airbender.Compiler.Captures.KeccakChi5

import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_chi5_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "keccak-chi5", format_version := 1 }

end Airbender.Compiler.Captures.KeccakChi5

namespace Airbender.Compiler

/-- The cached split worker has the same constraint description as its no-cache capture. -/
def KeccakChi5CachedDescriptionClaim : Prop :=
  { Captures.KeccakChi5.imported.circuit with layers := Airbender.Keccak.Split.Chi5.importedCircuit.layers } =
    Airbender.Keccak.Split.Chi5.importedCircuit

/-- Native base-field equations and source placement imply every description equation. -/
def KeccakChi5CachedArithmeticClaim : Prop :=
  ∀ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.KeccakChi5.imported.circuit physical →
    NativeArithmetic.PlacementAgreement Captures.KeccakChi5.imported.circuit physical logical →
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations Captures.KeccakChi5.imported.circuit)

end Airbender.Compiler

namespace Airbender.Compiler

/-- Native arithmetic and source placement have a concrete assignment. -/
def KeccakChi5CachedArithmeticSatisfiableClaim : Prop :=
  ∃ (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F),
    NativeArithmetic.Holds Captures.KeccakChi5.imported.circuit physical ∧
    NativeArithmetic.PlacementAgreement Captures.KeccakChi5.imported.circuit physical logical

end Airbender.Compiler
