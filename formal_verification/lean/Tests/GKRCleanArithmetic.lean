import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.AddSubUncached

namespace Tests.GKRCleanArithmetic
open Airbender Airbender.Compiler
open Airbender.Compiler.CleanArithmeticNative.AddSubUncached
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
local instance : Field Source.BaseField := ZMod.instField _
local instance : DecidableEq Source.BaseField := ZMod.decidableEq _

theorem rejects_replacement_clean_expression :
    equal (CleanExpression.polynomial native.placement (_root_.Expression.const (1 : Source.BaseField)))
      (combination native.relations native.witness0) = false := by decide +kernel

theorem rejects_wrong_logical_placement :
    equal (CleanExpression.polynomial
      (fun index => if index = 4 then native.placement 0 else native.placement index) native.expression0)
      (combination native.relations native.witness0) = false := by decide +kernel

end Tests.GKRCleanArithmetic
