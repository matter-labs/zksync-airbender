module
public import Proven.OpIndex
public import Human.Circuits.Blake2Round.Artifact
public import Mathlib.Data.Nat.Bitwise
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2Round.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2Round.importedConstraintsTimestampLookups
