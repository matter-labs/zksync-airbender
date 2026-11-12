module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part035
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

local instance generatedBatch36Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch36Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness32 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨94, by decide⟩)]

theorem native.idealCodeBinding32 :
    CleanIdealChecks.encode native.placement native.expression32 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 32 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding32 :
    NumericPolynomialChecks.encodeCombination native.witness32 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 32 [] := by kernel_rfl

theorem native.idealInputsBinding32 :
    CleanExpression.inputs native.expression32 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 32 [] := by kernel_rfl

theorem native.checked32 :
    equal (CleanExpression.polynomial native.placement native.expression32)
        (combination native.relations native.witness32) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression32 native.witness32
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 32
    (by decide +kernel) native.idealCodeBinding32 native.idealRelationsBinding native.idealWitnessBinding32

theorem native.preserved32 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression32).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression32 native.placement native.relations native.witness32
    native.checked32 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
