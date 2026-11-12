module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part029
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

local instance generatedBatch30Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch30Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness29 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨91, by decide⟩)]

theorem native.idealCodeBinding29 :
    CleanIdealChecks.encode native.placement native.expression29 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 29 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding29 :
    NumericPolynomialChecks.encodeCombination native.witness29 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 29 [] := by kernel_rfl

theorem native.idealInputsBinding29 :
    CleanExpression.inputs native.expression29 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 29 [] := by kernel_rfl

theorem native.checked29 :
    equal (CleanExpression.polynomial native.placement native.expression29)
        (combination native.relations native.witness29) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression29 native.witness29
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 29
    (by decide +kernel) native.idealCodeBinding29 native.idealRelationsBinding native.idealWitnessBinding29

theorem native.preserved29 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression29).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression29 native.placement native.relations native.witness29
    native.checked29 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
