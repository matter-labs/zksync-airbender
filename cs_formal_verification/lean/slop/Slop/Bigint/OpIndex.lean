import Slop.OpIndex
import Slop.Bigint.ArtifactChecks

set_option maxRecDepth 100000 in
derive_op_index Airbender.Bigint.importedConstraints
