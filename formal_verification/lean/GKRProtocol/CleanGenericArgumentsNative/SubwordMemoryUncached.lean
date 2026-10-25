import GKRProtocol.CleanGenericArgumentsParts.SubwordMemoryUncached.Part0

namespace Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

noncomputable def genericExpressions0 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression0_0, part0.genericExpression0_1, part0.genericExpression0_2, part0.genericExpression0_3, part0.genericExpression0_4, part0.genericExpression0_5, part0.genericExpression0_6, part0.genericExpression0_7, part0.genericExpression0_8]

noncomputable def genericExpressions1 : Vector (_root_.Expression Source.BaseField) 9 :=
  #v[part0.genericExpression1_0, part0.genericExpression1_1, part0.genericExpression1_2, part0.genericExpression1_3, part0.genericExpression1_4, part0.genericExpression1_5, part0.genericExpression1_6, part0.genericExpression1_7, part0.genericExpression1_8]

noncomputable def genericExpressions : List (Vector (_root_.Expression Source.BaseField) 9) :=
  [genericExpressions0, genericExpressions1]

end Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native
