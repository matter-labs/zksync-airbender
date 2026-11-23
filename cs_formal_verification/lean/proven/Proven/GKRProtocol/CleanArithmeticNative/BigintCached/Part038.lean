module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part037
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

local instance generatedBatch38Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch38Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness33 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨95, by decide⟩)]

theorem native.idealCodeBinding33 :
    CleanIdealChecks.encode native.placement native.expression33 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 33 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding33 :
    NumericPolynomialChecks.encodeCombination native.witness33 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 33 [] := by kernel_rfl

theorem native.idealInputsBinding33 :
    CleanExpression.inputs native.expression33 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 33 [] := by kernel_rfl

theorem native.checked33 :
    equal (CleanExpression.polynomial native.placement native.expression33)
        (combination native.relations native.witness33) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression33 native.witness33
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 33
    (by decide +kernel) native.idealCodeBinding33 native.idealRelationsBinding native.idealWitnessBinding33

theorem native.preserved33 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression33).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression33 native.placement native.relations native.witness33
    native.checked33 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
