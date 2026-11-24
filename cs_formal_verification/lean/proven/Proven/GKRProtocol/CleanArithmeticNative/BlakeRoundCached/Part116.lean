module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part115
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

local instance generatedBatch116Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch116Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved207 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression207).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression207 native.placement native.relations native.witness207
    native.checked207 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression208 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨727⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨727⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness208 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨298, by decide⟩)]

theorem native.idealCodeBinding208 :
    CleanIdealChecks.encode native.placement native.expression208 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 208 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding208 :
    NumericPolynomialChecks.encodeCombination native.witness208 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 208 [] := by kernel_rfl

theorem native.idealInputsBinding208 :
    CleanExpression.inputs native.expression208 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 208 [] := by kernel_rfl

theorem native.checked208 :
    equal (CleanExpression.polynomial native.placement native.expression208)
        (combination native.relations native.witness208) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression208 native.witness208
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 208 (by decide +kernel) native.idealCodeBinding208
    native.idealRelationsBinding native.idealWitnessBinding208

theorem native.preserved208 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression208).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression208 native.placement native.relations native.witness208
    native.checked208 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression209 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨730⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨730⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness209 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨299, by decide⟩)]

theorem native.idealCodeBinding209 :
    CleanIdealChecks.encode native.placement native.expression209 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 209 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding209 :
    NumericPolynomialChecks.encodeCombination native.witness209 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 209 [] := by kernel_rfl

theorem native.idealInputsBinding209 :
    CleanExpression.inputs native.expression209 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 209 [] := by kernel_rfl

theorem native.checked209 :
    equal (CleanExpression.polynomial native.placement native.expression209)
        (combination native.relations native.witness209) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression209 native.witness209
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 209 (by decide +kernel) native.idealCodeBinding209
    native.idealRelationsBinding native.idealWitnessBinding209

theorem native.preserved209 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression209).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression209 native.placement native.relations native.witness209
    native.checked209 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression210 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨733⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨733⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness210 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨300, by decide⟩)]

theorem native.idealCodeBinding210 :
    CleanIdealChecks.encode native.placement native.expression210 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 210 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding210 :
    NumericPolynomialChecks.encodeCombination native.witness210 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 210 [] := by kernel_rfl

theorem native.idealInputsBinding210 :
    CleanExpression.inputs native.expression210 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 210 [] := by kernel_rfl

theorem native.checked210 :
    equal (CleanExpression.polynomial native.placement native.expression210)
        (combination native.relations native.witness210) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression210 native.witness210
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 210 (by decide +kernel) native.idealCodeBinding210
    native.idealRelationsBinding native.idealWitnessBinding210

theorem native.preserved210 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression210).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression210 native.placement native.relations native.witness210
    native.checked210 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression211 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨736⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨736⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness211 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨301, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
