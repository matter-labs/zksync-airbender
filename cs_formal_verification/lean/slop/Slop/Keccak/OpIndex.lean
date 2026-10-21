import Slop.OpIndex
import Human.Circuits.Keccak.Artifact

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.importedConstraints

set_option maxRecDepth 100000 in
derive_op_index Airbender.Keccak.importedConstraintsTimestampLookups
