module
public import Human.Compiler.Capture
public import Human.Import.TranscribeCommand
public import Human.Compiler.NativeArithmetic
public import Human.Circuits.KeccakSplit.ThetaRho.Artifact

@[expose] public section
namespace Airbender.Compiler.Captures.KeccakThetaRho

import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_theta_rho_layout_gkr.json" shared imported

noncomputable def imported : NativeCapture := {
  cached := true, circuit := importedCircuit, family := "keccak-theta-rho", format_version := 1 }

end Airbender.Compiler.Captures.KeccakThetaRho
