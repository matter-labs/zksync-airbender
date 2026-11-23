module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part047
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

local instance generatedBatch48Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch48Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness38 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨100, by decide⟩)]

theorem native.idealCodeBinding38 :
    CleanIdealChecks.encode native.placement native.expression38 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 38 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding38 :
    NumericPolynomialChecks.encodeCombination native.witness38 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 38 [] := by kernel_rfl

theorem native.idealInputsBinding38 :
    CleanExpression.inputs native.expression38 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 38 [] := by kernel_rfl

theorem native.checked38 :
    equal (CleanExpression.polynomial native.placement native.expression38)
        (combination native.relations native.witness38) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression38 native.witness38
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 38
    (by decide +kernel) native.idealCodeBinding38 native.idealRelationsBinding native.idealWitnessBinding38

theorem native.preserved38 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression38).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression38 native.placement native.relations native.witness38
    native.checked38 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
