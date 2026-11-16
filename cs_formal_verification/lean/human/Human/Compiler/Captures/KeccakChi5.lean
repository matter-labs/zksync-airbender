module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Circuits.KeccakSplit.Chi5.Artifact

@[expose] public section
namespace Airbender.Compiler.Captures.KeccakChi5

import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_chi5_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "keccak-chi5", format_version := 1 }

end Airbender.Compiler.Captures.KeccakChi5
