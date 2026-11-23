module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part053
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

local instance generatedBatch54Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch54Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness41 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨103, by decide⟩)]

theorem native.idealCodeBinding41 :
    CleanIdealChecks.encode native.placement native.expression41 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 41 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding41 :
    NumericPolynomialChecks.encodeCombination native.witness41 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 41 [] := by kernel_rfl

theorem native.idealInputsBinding41 :
    CleanExpression.inputs native.expression41 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 41 [] := by kernel_rfl

theorem native.checked41 :
    equal (CleanExpression.polynomial native.placement native.expression41)
        (combination native.relations native.witness41) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression41 native.witness41
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 41
    (by decide +kernel) native.idealCodeBinding41 native.idealRelationsBinding native.idealWitnessBinding41

theorem native.preserved41 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression41).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression41 native.placement native.relations native.witness41
    native.checked41 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
