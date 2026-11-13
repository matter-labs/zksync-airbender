module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part031
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

local instance generatedBatch32Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch32Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness30 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨92, by decide⟩)]

theorem native.idealCodeBinding30 :
    CleanIdealChecks.encode native.placement native.expression30 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 30 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding30 :
    NumericPolynomialChecks.encodeCombination native.witness30 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 30 [] := by kernel_rfl

theorem native.idealInputsBinding30 :
    CleanExpression.inputs native.expression30 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 30 [] := by kernel_rfl

theorem native.checked30 :
    equal (CleanExpression.polynomial native.placement native.expression30)
        (combination native.relations native.witness30) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression30 native.witness30
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 30
    (by decide +kernel) native.idealCodeBinding30 native.idealRelationsBinding native.idealWitnessBinding30

theorem native.preserved30 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression30).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression30 native.placement native.relations native.witness30
    native.checked30 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
