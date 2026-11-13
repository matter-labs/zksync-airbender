module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part043
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

local instance generatedBatch44Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch44Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness36 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨98, by decide⟩)]

theorem native.idealCodeBinding36 :
    CleanIdealChecks.encode native.placement native.expression36 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 36 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding36 :
    NumericPolynomialChecks.encodeCombination native.witness36 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 36 [] := by kernel_rfl

theorem native.idealInputsBinding36 :
    CleanExpression.inputs native.expression36 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 36 [] := by kernel_rfl

theorem native.checked36 :
    equal (CleanExpression.polynomial native.placement native.expression36)
        (combination native.relations native.witness36) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression36 native.witness36
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 36
    (by decide +kernel) native.idealCodeBinding36 native.idealRelationsBinding native.idealWitnessBinding36

theorem native.preserved36 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression36).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression36 native.placement native.relations native.witness36
    native.checked36 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
