module
public import Slop.OpIndex
public import Human.Circuits.KeccakSplit.ThetaRho.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.ThetaRho.importedConstraints
