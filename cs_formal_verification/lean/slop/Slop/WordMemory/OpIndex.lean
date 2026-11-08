module
public import Slop.OpIndex
public import Human.Circuits.WordMemory.Artifact

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.WordMemory.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.WordMemory.importedConstraintsTimestampLookups
