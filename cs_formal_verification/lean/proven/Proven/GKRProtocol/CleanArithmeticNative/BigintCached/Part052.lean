module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part051
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

local instance generatedBatch52Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch52Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness40 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨102, by decide⟩)]

theorem native.idealCodeBinding40 :
    CleanIdealChecks.encode native.placement native.expression40 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 40 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding40 :
    NumericPolynomialChecks.encodeCombination native.witness40 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 40 [] := by kernel_rfl

theorem native.idealInputsBinding40 :
    CleanExpression.inputs native.expression40 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 40 [] := by kernel_rfl

theorem native.checked40 :
    equal (CleanExpression.polynomial native.placement native.expression40)
        (combination native.relations native.witness40) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression40 native.witness40
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 40
    (by decide +kernel) native.idealCodeBinding40 native.idealRelationsBinding native.idealWitnessBinding40

theorem native.preserved40 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression40).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression40 native.placement native.relations native.witness40
    native.checked40 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
