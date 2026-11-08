module
public import Slop.OpIndex
public import Human.Circuits.JumpBranchSlt.Artifact

@[expose] public section

set_option maxRecDepth 100000 in
derive_op_index Airbender.JumpBranchSlt.importedConstraints
