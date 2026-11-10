module
public import Slop.OpIndex
public import Human.Circuits.ShiftBinop.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.ShiftBinop.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.ShiftBinop.importedConstraintsTimestampLookups
