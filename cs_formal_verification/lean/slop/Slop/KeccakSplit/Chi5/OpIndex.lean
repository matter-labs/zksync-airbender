module
public import Slop.OpIndex
public import Human.Circuits.KeccakSplit.Chi5.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.Chi5.importedConstraints
