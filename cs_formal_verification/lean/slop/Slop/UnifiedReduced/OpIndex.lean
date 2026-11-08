module
public import Slop.OpIndex
public import Human.Circuits.UnifiedReduced.Artifact

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.importedConstraintsTimestampLookups
