module
public import Slop.OpIndex
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact
public import Human.Circuits.KeccakSplit.ThetaRho.Artifact
public import Human.Circuits.KeccakSplit.Chi5.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-! Literal-index lemmas (`op_index`) for the timestamp queries of the three split-Keccak workers. -/

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.ColumnParity.importedConstraintsTimestampLookups

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.ThetaRho.importedConstraintsTimestampLookups

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.Split.Chi5.importedConstraintsTimestampLookups
