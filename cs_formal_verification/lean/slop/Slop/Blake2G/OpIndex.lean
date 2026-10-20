import Slop.OpIndex
import Slop.Blake2G.Fragment

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.Proofs.mixingConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Blake2G.importedConstraints
