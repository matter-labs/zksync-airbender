module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part023
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

local instance generatedBatch24Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch24Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness26 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨88, by decide⟩)]

theorem native.idealCodeBinding26 :
    CleanIdealChecks.encode native.placement native.expression26 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 26 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding26 :
    NumericPolynomialChecks.encodeCombination native.witness26 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 26 [] := by kernel_rfl

theorem native.idealInputsBinding26 :
    CleanExpression.inputs native.expression26 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 26 [] := by kernel_rfl

theorem native.checked26 :
    equal (CleanExpression.polynomial native.placement native.expression26)
        (combination native.relations native.witness26) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression26 native.witness26
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 26
    (by decide +kernel) native.idealCodeBinding26 native.idealRelationsBinding native.idealWitnessBinding26

theorem native.preserved26 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression26).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression26 native.placement native.relations native.witness26
    native.checked26 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
