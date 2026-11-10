module
public import Slop.OpIndex
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.ColumnParity.importedConstraints
