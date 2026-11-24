module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part025
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

local instance generatedBatch26Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch26Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness27 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨89, by decide⟩)]

theorem native.idealCodeBinding27 :
    CleanIdealChecks.encode native.placement native.expression27 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 27 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding27 :
    NumericPolynomialChecks.encodeCombination native.witness27 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 27 [] := by kernel_rfl

theorem native.idealInputsBinding27 :
    CleanExpression.inputs native.expression27 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 27 [] := by kernel_rfl

theorem native.checked27 :
    equal (CleanExpression.polynomial native.placement native.expression27)
        (combination native.relations native.witness27) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression27 native.witness27
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 27
    (by decide +kernel) native.idealCodeBinding27 native.idealRelationsBinding native.idealWitnessBinding27

theorem native.preserved27 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression27).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression27 native.placement native.relations native.witness27
    native.checked27 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
