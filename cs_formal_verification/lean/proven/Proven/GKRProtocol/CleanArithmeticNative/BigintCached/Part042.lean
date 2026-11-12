module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part041
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch42Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch42Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness35 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨97, by decide⟩)]

theorem native.idealCodeBinding35 :
    CleanIdealChecks.encode native.placement native.expression35 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 35 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding35 :
    NumericPolynomialChecks.encodeCombination native.witness35 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 35 [] := by kernel_rfl

theorem native.idealInputsBinding35 :
    CleanExpression.inputs native.expression35 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 35 [] := by kernel_rfl

theorem native.checked35 :
    equal (CleanExpression.polynomial native.placement native.expression35)
        (combination native.relations native.witness35) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression35 native.witness35
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 35
    (by decide +kernel) native.idealCodeBinding35 native.idealRelationsBinding native.idealWitnessBinding35

theorem native.preserved35 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression35).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression35 native.placement native.relations native.witness35
    native.checked35 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
