module
public import Proven.OpIndex
public import Human.Circuits.MulDiv.Artifact
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.MulDiv.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.MulDiv.importedConstraintsTimestampLookups
