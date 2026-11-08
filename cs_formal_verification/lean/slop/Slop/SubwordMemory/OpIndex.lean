module
public import Slop.OpIndex
public import Human.Circuits.SubwordMemory.Artifact

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.SubwordMemory.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.SubwordMemory.importedConstraintsTimestampLookups
