module
public import Proven.OpIndex
public import Proven.Bigint.ArtifactChecks
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Bigint.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Bigint.importedConstraintsTimestampLookups
