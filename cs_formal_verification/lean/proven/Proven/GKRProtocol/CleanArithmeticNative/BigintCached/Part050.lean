module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part049
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

local instance generatedBatch50Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch50Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness39 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨101, by decide⟩)]

theorem native.idealCodeBinding39 :
    CleanIdealChecks.encode native.placement native.expression39 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 39 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding39 :
    NumericPolynomialChecks.encodeCombination native.witness39 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 39 [] := by kernel_rfl

theorem native.idealInputsBinding39 :
    CleanExpression.inputs native.expression39 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 39 [] := by kernel_rfl

theorem native.checked39 :
    equal (CleanExpression.polynomial native.placement native.expression39)
        (combination native.relations native.witness39) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression39 native.witness39
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 39
    (by decide +kernel) native.idealCodeBinding39 native.idealRelationsBinding native.idealWitnessBinding39

theorem native.preserved39 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression39).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression39 native.placement native.relations native.witness39
    native.checked39 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
