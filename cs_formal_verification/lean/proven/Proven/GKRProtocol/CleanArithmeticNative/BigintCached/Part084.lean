module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part083
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

local instance generatedBatch84Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch84Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved126 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression126).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression126 native.placement native.relations native.witness126
    native.checked126 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression127 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨251⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨251⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness127 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨168, by decide⟩)]

theorem native.idealCodeBinding127 :
    CleanIdealChecks.encode native.placement native.expression127 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 127 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding127 :
    NumericPolynomialChecks.encodeCombination native.witness127 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 127 [] := by kernel_rfl

theorem native.idealInputsBinding127 :
    CleanExpression.inputs native.expression127 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 127 [] := by kernel_rfl

theorem native.checked127 :
    equal (CleanExpression.polynomial native.placement native.expression127)
        (combination native.relations native.witness127) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression127 native.witness127
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    127 (by decide +kernel) native.idealCodeBinding127 native.idealRelationsBinding native.idealWitnessBinding127

theorem native.preserved127 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression127).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression127 native.placement native.relations native.witness127
    native.checked127 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression128 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨254⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨254⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness128 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨169, by decide⟩)]

theorem native.idealCodeBinding128 :
    CleanIdealChecks.encode native.placement native.expression128 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 128 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding128 :
    NumericPolynomialChecks.encodeCombination native.witness128 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 128 [] := by kernel_rfl

theorem native.idealInputsBinding128 :
    CleanExpression.inputs native.expression128 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 128 [] := by kernel_rfl

theorem native.checked128 :
    equal (CleanExpression.polynomial native.placement native.expression128)
        (combination native.relations native.witness128) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression128 native.witness128
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    128 (by decide +kernel) native.idealCodeBinding128 native.idealRelationsBinding native.idealWitnessBinding128

theorem native.preserved128 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression128).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression128 native.placement native.relations native.witness128
    native.checked128 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression129 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨257⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨257⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness129 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨170, by decide⟩)]

theorem native.idealCodeBinding129 :
    CleanIdealChecks.encode native.placement native.expression129 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 129 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding129 :
    NumericPolynomialChecks.encodeCombination native.witness129 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 129 [] := by kernel_rfl

theorem native.idealInputsBinding129 :
    CleanExpression.inputs native.expression129 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 129 [] := by kernel_rfl

theorem native.checked129 :
    equal (CleanExpression.polynomial native.placement native.expression129)
        (combination native.relations native.witness129) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression129 native.witness129
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    129 (by decide +kernel) native.idealCodeBinding129 native.idealRelationsBinding native.idealWitnessBinding129

theorem native.preserved129 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression129).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression129 native.placement native.relations native.witness129
    native.checked129 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression130 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨260⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨260⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness130 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨171, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BigintCached
