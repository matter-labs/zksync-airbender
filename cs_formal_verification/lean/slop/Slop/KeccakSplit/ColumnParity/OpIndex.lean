module
public import Slop.OpIndex
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.ColumnParity.importedConstraints
