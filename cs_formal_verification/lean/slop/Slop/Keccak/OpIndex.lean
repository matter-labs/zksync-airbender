module
public import Slop.OpIndex
public import Human.Circuits.Keccak.Artifact

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.importedConstraintsTimestampLookups
