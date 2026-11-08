module
public import Slop.OpIndex
public import Slop.Blake2Round.ArtifactChecks

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2Round.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2Round.importedConstraintsTimestampLookups
