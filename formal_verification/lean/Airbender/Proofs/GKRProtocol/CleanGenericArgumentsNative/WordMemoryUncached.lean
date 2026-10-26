import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsParts.WordMemoryUncached.Part0

namespace Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

noncomputable def genericExpressions0 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression0_0, part0.genericExpression0_1, part0.genericExpression0_2, part0.genericExpression0_3, part0.genericExpression0_4, part0.genericExpression0_5, part0.genericExpression0_6, part0.genericExpression0_7, part0.genericExpression0_8]

noncomputable def genericExpressions : List (Vector (_root_.Expression Source.BaseField) 9) :=
  [genericExpressions0]

end Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native
