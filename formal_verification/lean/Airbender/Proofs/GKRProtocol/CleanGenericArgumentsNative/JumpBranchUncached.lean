import Airbender.Proofs.GKRProtocol.CleanGenericArgumentsParts.JumpBranchUncached.Part0

namespace Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

noncomputable def genericExpressions0 : Vector (_root_.Expression Source.BaseField) 10 :=
  #v[part0.genericExpression0_0, part0.genericExpression0_1, part0.genericExpression0_2, part0.genericExpression0_3, part0.genericExpression0_4, part0.genericExpression0_5, part0.genericExpression0_6, part0.genericExpression0_7, part0.genericExpression0_8, part0.genericExpression0_9]

noncomputable def genericExpressions1 : Vector (_root_.Expression Source.BaseField) 10 :=
  #v[part0.genericExpression1_0, part0.genericExpression1_1, part0.genericExpression1_2, part0.genericExpression1_3, part0.genericExpression1_4, part0.genericExpression1_5, part0.genericExpression1_6, part0.genericExpression1_7, part0.genericExpression1_8, part0.genericExpression1_9]

noncomputable def genericExpressions2 : Vector (_root_.Expression Source.BaseField) 10 :=
  #v[part0.genericExpression2_0, part0.genericExpression2_1, part0.genericExpression2_2, part0.genericExpression2_3, part0.genericExpression2_4, part0.genericExpression2_5, part0.genericExpression2_6, part0.genericExpression2_7, part0.genericExpression2_8, part0.genericExpression2_9]

noncomputable def genericExpressions3 : Vector (_root_.Expression Source.BaseField) 10 :=
  #v[part0.genericExpression3_0, part0.genericExpression3_1, part0.genericExpression3_2, part0.genericExpression3_3, part0.genericExpression3_4, part0.genericExpression3_5, part0.genericExpression3_6, part0.genericExpression3_7, part0.genericExpression3_8, part0.genericExpression3_9]

noncomputable def genericExpressions : List (Vector (_root_.Expression Source.BaseField) 10) :=
  [genericExpressions0, genericExpressions1, genericExpressions2, genericExpressions3]

end Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native
