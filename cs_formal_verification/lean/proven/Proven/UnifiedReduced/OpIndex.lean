module
public import Proven.OpIndex
public import Human.Circuits.UnifiedReduced.Artifact
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.importedConstraintsTimestampLookups
