module
public import Human.Compiler.LookupSelectors
public import Human.Compiler.WorkerLookups
public import Human.Compiler.Captures.Keccak
public import Human.Circuits.InitsTeardowns.SharedArtifact
public meta import Lean

set_option warningAsError true

/- Shared captures retain their circuit but do not retain unused layout text. -/
run_cmd do
  let environment ← Lean.getEnv
  for family in #["AddSub", "Bigint", "BlakeG", "BlakeRound", "JumpBranch", "Keccak",
      "MulDiv", "ShiftBinop", "SubwordMemory", "Unified", "WordMemory",
      "KeccakColumnParity", "KeccakThetaRho", "KeccakChi5"] do
    let circuit := ("Airbender.Compiler.Captures." ++ family ++ ".importedCircuit").toName
    unless environment.contains circuit do
      throwError "The cached circuit is missing: {circuit}"
    if environment.contains (circuit.appendAfter "SourceBytes") then
      throwError "The shared capture retains unused layout text: {circuit}"
  unless environment.contains `Airbender.AddSub.importedCircuitSourceBytes do
    throwError "The source-bound import must retain its layout text"
  unless environment.contains `Airbender.InitsTeardowns.sharedLayoutCircuitBytes do
    throwError "The shared inits/teardowns import must retain the bytes that SharedBytesClaim reads"
  if environment.contains `Airbender.InitsTeardowns.sharedLayoutCircuitSourceBytes then
    throwError "The shared inits/teardowns import retains unused layout text"
