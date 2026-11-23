module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part027
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

local instance generatedBatch28Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch28Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness28 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨90, by decide⟩)]

theorem native.idealCodeBinding28 :
    CleanIdealChecks.encode native.placement native.expression28 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 28 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding28 :
    NumericPolynomialChecks.encodeCombination native.witness28 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 28 [] := by kernel_rfl

theorem native.idealInputsBinding28 :
    CleanExpression.inputs native.expression28 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 28 [] := by kernel_rfl

theorem native.checked28 :
    equal (CleanExpression.polynomial native.placement native.expression28)
        (combination native.relations native.witness28) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression28 native.witness28
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 28
    (by decide +kernel) native.idealCodeBinding28 native.idealRelationsBinding native.idealWitnessBinding28

theorem native.preserved28 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression28).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression28 native.placement native.relations native.witness28
    native.checked28 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
