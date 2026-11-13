module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part045
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

local instance generatedBatch46Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch46Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness37 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨99, by decide⟩)]

theorem native.idealCodeBinding37 :
    CleanIdealChecks.encode native.placement native.expression37 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 37 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding37 :
    NumericPolynomialChecks.encodeCombination native.witness37 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 37 [] := by kernel_rfl

theorem native.idealInputsBinding37 :
    CleanExpression.inputs native.expression37 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 37 [] := by kernel_rfl

theorem native.checked37 :
    equal (CleanExpression.polynomial native.placement native.expression37)
        (combination native.relations native.witness37) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression37 native.witness37
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 37
    (by decide +kernel) native.idealCodeBinding37 native.idealRelationsBinding native.idealWitnessBinding37

theorem native.preserved37 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression37).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression37 native.placement native.relations native.witness37
    native.checked37 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
