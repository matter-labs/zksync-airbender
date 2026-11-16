module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact

@[expose] public section
namespace Airbender.Compiler.Captures.KeccakColumnParity

import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_column_parity_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "keccak-column-parity", format_version := 1 }

end Airbender.Compiler.Captures.KeccakColumnParity
