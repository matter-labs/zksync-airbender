module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part033
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

local instance generatedBatch34Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch34Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness31 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨93, by decide⟩)]

theorem native.idealCodeBinding31 :
    CleanIdealChecks.encode native.placement native.expression31 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 31 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding31 :
    NumericPolynomialChecks.encodeCombination native.witness31 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 31 [] := by kernel_rfl

theorem native.idealInputsBinding31 :
    CleanExpression.inputs native.expression31 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 31 [] := by kernel_rfl

theorem native.checked31 :
    equal (CleanExpression.polynomial native.placement native.expression31)
        (combination native.relations native.witness31) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression31 native.witness31
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 31
    (by decide +kernel) native.idealCodeBinding31 native.idealRelationsBinding native.idealWitnessBinding31

theorem native.preserved31 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression31).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression31 native.placement native.relations native.witness31
    native.checked31 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
