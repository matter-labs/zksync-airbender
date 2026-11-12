module
public import Slop.OpIndex
public import Slop.Blake2G.Fragment
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.Proofs.mixingConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.importedConstraintsTimestampLookups
