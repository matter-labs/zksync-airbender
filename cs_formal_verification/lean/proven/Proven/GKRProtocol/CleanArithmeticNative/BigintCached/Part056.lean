module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part055
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

local instance generatedBatch56Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch56Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness42 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨104, by decide⟩)]

theorem native.idealCodeBinding42 :
    CleanIdealChecks.encode native.placement native.expression42 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 42 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding42 :
    NumericPolynomialChecks.encodeCombination native.witness42 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 42 [] := by kernel_rfl

theorem native.idealInputsBinding42 :
    CleanExpression.inputs native.expression42 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 42 [] := by kernel_rfl

theorem native.checked42 :
    equal (CleanExpression.polynomial native.placement native.expression42)
        (combination native.relations native.witness42) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression42 native.witness42
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 42
    (by decide +kernel) native.idealCodeBinding42 native.idealRelationsBinding native.idealWitnessBinding42

theorem native.preserved42 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression42).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression42 native.placement native.relations native.witness42
    native.checked42 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
