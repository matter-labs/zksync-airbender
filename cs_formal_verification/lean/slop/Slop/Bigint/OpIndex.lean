module
public import Slop.OpIndex
public import Slop.Bigint.ArtifactChecks
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Bigint.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Bigint.importedConstraintsTimestampLookups
