module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part039
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

local instance generatedBatch40Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch40Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness34 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨96, by decide⟩)]

theorem native.idealCodeBinding34 :
    CleanIdealChecks.encode native.placement native.expression34 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 34 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding34 :
    NumericPolynomialChecks.encodeCombination native.witness34 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 34 [] := by kernel_rfl

theorem native.idealInputsBinding34 :
    CleanExpression.inputs native.expression34 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 34 [] := by kernel_rfl

theorem native.checked34 :
    equal (CleanExpression.polynomial native.placement native.expression34)
        (combination native.relations native.witness34) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression34 native.witness34
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 34
    (by decide +kernel) native.idealCodeBinding34 native.idealRelationsBinding native.idealWitnessBinding34

theorem native.preserved34 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression34).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression34 native.placement native.relations native.witness34
    native.checked34 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
