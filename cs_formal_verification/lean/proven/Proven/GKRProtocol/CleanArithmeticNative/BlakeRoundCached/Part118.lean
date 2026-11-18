module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part117
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch118Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch118Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked214 :
    equal (CleanExpression.polynomial native.placement native.expression214)
        (combination native.relations native.witness214) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression214 native.witness214
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 214 (by decide +kernel) native.idealCodeBinding214
    native.idealRelationsBinding native.idealWitnessBinding214

theorem native.preserved214 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression214).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression214 native.placement native.relations native.witness214
    native.checked214 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression215 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨748⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨748⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness215 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨305, by decide⟩)]

theorem native.idealCodeBinding215 :
    CleanIdealChecks.encode native.placement native.expression215 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 215 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding215 :
    NumericPolynomialChecks.encodeCombination native.witness215 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 215 [] := by kernel_rfl

theorem native.idealInputsBinding215 :
    CleanExpression.inputs native.expression215 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 215 [] := by kernel_rfl

theorem native.checked215 :
    equal (CleanExpression.polynomial native.placement native.expression215)
        (combination native.relations native.witness215) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression215 native.witness215
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 215 (by decide +kernel) native.idealCodeBinding215
    native.idealRelationsBinding native.idealWitnessBinding215

theorem native.preserved215 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression215).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression215 native.placement native.relations native.witness215
    native.checked215 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression216 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨751⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨751⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness216 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨306, by decide⟩)]

theorem native.idealCodeBinding216 :
    CleanIdealChecks.encode native.placement native.expression216 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 216 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding216 :
    NumericPolynomialChecks.encodeCombination native.witness216 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 216 [] := by kernel_rfl

theorem native.idealInputsBinding216 :
    CleanExpression.inputs native.expression216 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 216 [] := by kernel_rfl

theorem native.checked216 :
    equal (CleanExpression.polynomial native.placement native.expression216)
        (combination native.relations native.witness216) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression216 native.witness216
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 216 (by decide +kernel) native.idealCodeBinding216
    native.idealRelationsBinding native.idealWitnessBinding216

theorem native.preserved216 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression216).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression216 native.placement native.relations native.witness216
    native.checked216 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression217 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨754⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨754⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness217 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨307, by decide⟩)]

theorem native.idealCodeBinding217 :
    CleanIdealChecks.encode native.placement native.expression217 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 217 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding217 :
    NumericPolynomialChecks.encodeCombination native.witness217 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 217 [] := by kernel_rfl

theorem native.idealInputsBinding217 :
    CleanExpression.inputs native.expression217 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 217 [] := by kernel_rfl

theorem native.checked217 :
    equal (CleanExpression.polynomial native.placement native.expression217)
        (combination native.relations native.witness217) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression217 native.witness217
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 217 (by decide +kernel) native.idealCodeBinding217
    native.idealRelationsBinding native.idealWitnessBinding217

theorem native.preserved217 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression217).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression217 native.placement native.relations native.witness217
    native.checked217 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression218 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨757⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨757⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
