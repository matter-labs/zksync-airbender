module
public import Proven.OpIndex
public import Proven.Blake2G.Fragment
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.Proofs.mixingConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.importedConstraintsTimestampLookups
